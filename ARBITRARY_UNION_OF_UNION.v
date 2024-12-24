Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARBITRARY_UNION_OF_UNION_term_abbrevs.
Require Import ARBITRARY_UNION_OF_UNIONS_spec.
Require Import FORALL_IN_INSERT_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import UNIONS_2_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem4868515 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4868516 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem4868517 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem4868516 A x) (@lem4868515 A x)). Qed.
Lemma lem4868518 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4868523 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem4868524 {A : Type'} (P : type686 A) (h1 : term3 A) : term4 A P.
Proof. exact (@lem4868523 A h1 P). Qed.
Lemma lem4868525 {A : Type'} (P : type686 A) : (term4 A P) = (term5 A P).
Proof. exact (eq_refl (term4 A P)). Qed.
Lemma lem4868526 {A : Type'} (P : type686 A) (h1 : term3 A) : term5 A P.
Proof. exact (EQ_MP (@lem4868525 A P) (@lem4868524 A P h1)). Qed.
Lemma lem4868527 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term3 A) : term6 A P u.
Proof. exact (@lem4868526 A P h1 u). Qed.
Lemma lem4868528 {A : Type'} (P : type686 A) (u : type686 A) : (term6 A P u) = (term7 A P u).
Proof. exact (eq_refl (term6 A P u)). Qed.
Lemma lem4868529 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term3 A) : term7 A P u.
Proof. exact (EQ_MP (@lem4868528 A P u) (@lem4868527 A P u h1)). Qed.
Lemma lem4868530 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term8 A u P) : term8 A u P.
Proof. exact (h1). Qed.
Lemma lem4868531 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term8 A u P) (h2 : term3 A) : term9 A P u.
Proof. exact (@lem4868529 A P u h2 (@lem4868530 A u P h1)). Qed.
Lemma lem4868532 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term8 A u P) : term10 A P u.
Proof. exact (fun h0 : term3 A => @lem4868531 A u P h1 h0). Qed.
Lemma lem4868533 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem4868534 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term8 A u P) (h2 : term3 A) : term9 A P u.
Proof. exact (@lem4868532 A u P h1 (@lem4868533 A h2)). Qed.
Lemma lem4868535 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term3 A) : term7 A P u.
Proof. exact (fun h0 : term8 A u P => @lem4868534 A u P h0 h1). Qed.
Lemma lem4868536 {A : Type'} (P : type686 A) (h1 : term3 A) : term5 A P.
Proof. exact (fun u : type686 A => @lem4868535 A P u h1). Qed.
Lemma lem4868537 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (fun P : type686 A => @lem4868536 A P h1). Qed.
Lemma lem4868538 {A : Type'} : term11 A.
Proof. exact (fun h0 : term3 A => @lem4868537 A h0). Qed.
Lemma lem4868539 {A : Type'} : term3 A.
Proof. exact (@lem4868538 A (@lem4868514 A)). Qed.
Lemma lem4868540 {A : Type'} (P : type686 A) : term4 A P.
Proof. exact (@lem4868539 A P). Qed.
Lemma lem4868541 {A : Type'} (P : type686 A) : (term4 A P) = (term5 A P).
Proof. exact (eq_refl (term4 A P)). Qed.
Lemma lem4868542 {A : Type'} (P : type686 A) : term5 A P.
Proof. exact (EQ_MP (@lem4868541 A P) (@lem4868540 A P)). Qed.
Lemma lem4868543 {A : Type'} (P : type686 A) (u : type686 A) : term6 A P u.
Proof. exact (@lem4868542 A P u). Qed.
Lemma lem4868544 {A : Type'} (P : type686 A) (u : type686 A) : (term6 A P u) = (term7 A P u).
Proof. exact (eq_refl (term6 A P u)). Qed.
Lemma lem4868546 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (h1 : (term12 _86827 s t) = (@UNION _86827 s t)) : (term12 _86827 s t) = (@UNION _86827 s t).
Proof. exact (h1). Qed.
Lemma lem4868547 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (h1 : (term12 _86827 s t) = (@UNION _86827 s t)) : (@UNION _86827 s t) = (term12 _86827 s t).
Proof. exact (SYM (@lem4868546 _86827 s t h1)). Qed.
Lemma lem4868548 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (h1 : (@UNION _86827 s t) = (term12 _86827 s t)) : (@UNION _86827 s t) = (term12 _86827 s t).
Proof. exact (h1). Qed.
Lemma lem4868549 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (h1 : (@UNION _86827 s t) = (term12 _86827 s t)) : (term12 _86827 s t) = (@UNION _86827 s t).
Proof. exact (SYM (@lem4868548 _86827 s t h1)). Qed.
Lemma lem4868550 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : ((term12 _86827 s t) = (@UNION _86827 s t)) = ((@UNION _86827 s t) = (term12 _86827 s t)).
Proof. exact (prop_ext (fun h1 : (term12 _86827 s t) = (@UNION _86827 s t) => @lem4868547 _86827 s t h1) (fun h1 : (@UNION _86827 s t) = (term12 _86827 s t) => @lem4868549 _86827 s t h1)). Qed.
Lemma lem4868552 {_111767 : Type'} (s : _111767 -> Prop) (P : type686 _111767) (t : _111767 -> Prop) (h1 : term13 _111767 s P t) : term13 _111767 s P t.
Proof. exact (h1). Qed.
Lemma lem4868553 {_111767 : Type'} (P : type686 _111767) (t : _111767 -> Prop) (h1 : @UNION_OF _111767 (@ARBITRARY _111767) P t) : @UNION_OF _111767 (@ARBITRARY _111767) P t.
Proof. exact (h1). Qed.
Lemma lem4868554 {_111767 : Type'} (P : type686 _111767) (s : _111767 -> Prop) (h1 : @UNION_OF _111767 (@ARBITRARY _111767) P s) : @UNION_OF _111767 (@ARBITRARY _111767) P s.
Proof. exact (h1). Qed.
Lemma lem4868556 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : (@UNION _86827 s t) = (term12 _86827 s t).
Proof. exact (EQ_MP (@lem4868550 _86827 s t) (@lem3323992 _86827 s t)). Qed.
Lemma lem4868557 {_111767 : Type'} (s : _111767 -> Prop) (t : _111767 -> Prop) : (@UNION _111767 s t) = (term12 _111767 s t).
Proof. exact (@lem4868556 _111767 s t). Qed.
Lemma lem4868558 {_111767 : Type'} (P : type686 _111767) : (@UNION_OF _111767 (@ARBITRARY _111767) P) = (@UNION_OF _111767 (@ARBITRARY _111767) P).
Proof. exact (eq_refl (@UNION_OF _111767 (@ARBITRARY _111767) P)). Qed.
Lemma lem4868559 {_111767 : Type'} (P : type686 _111767) (s : _111767 -> Prop) (t : _111767 -> Prop) : (term14 _111767 P s t) = (term15 _111767 P s t).
Proof. exact (MK_COMB (@lem4868558 _111767 P) (@lem4868557 _111767 s t)). Qed.
Lemma lem4868560 {_111767 : Type'} (P : type686 _111767) (s : _111767 -> Prop) (t : _111767 -> Prop) : (term15 _111767 P s t) = (term14 _111767 P s t).
Proof. exact (SYM (@lem4868559 _111767 P s t)). Qed.
Lemma lem4868562 {A : Type'} (P : type686 A) (u : type686 A) : term7 A P u.
Proof. exact (EQ_MP (@lem4868544 A P u) (@lem4868543 A P u)). Qed.
Lemma lem4868563 {_111767 : Type'} (P : type686 _111767) (u : type686 _111767) : term7 _111767 P u.
Proof. exact (@lem4868562 _111767 P u). Qed.
Lemma lem4868564 {_111767 : Type'} (P : type686 _111767) (s : _111767 -> Prop) (t : _111767 -> Prop) : term16 _111767 P s t.
Proof. exact (@lem4868563 _111767 P (term17 _111767 s t)). Qed.
Lemma lem4868565 {_83983 : Type'} (P : _83983 -> Prop) : term18 _83983 P.
Proof. exact (@lem3207453 _83983 P). Qed.
Lemma lem4868566 {_83983 : Type'} (P : _83983 -> Prop) : (term18 _83983 P) = (term19 _83983 P).
Proof. exact (eq_refl (term18 _83983 P)). Qed.
Lemma lem4868567 {_83983 : Type'} (P : _83983 -> Prop) : term19 _83983 P.
Proof. exact (EQ_MP (@lem4868566 _83983 P) (@lem4868565 _83983 P)). Qed.
Lemma lem4868568 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : term20 _83983 P a.
Proof. exact (@lem4868567 _83983 P a). Qed.
Lemma lem4868569 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : (term20 _83983 P a) = (term21 _83983 a P).
Proof. exact (eq_refl (term20 _83983 P a)). Qed.
Lemma lem4868570 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : term21 _83983 a P.
Proof. exact (EQ_MP (@lem4868569 _83983 a P) (@lem4868568 _83983 P a)). Qed.
Lemma lem4868571 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (s : _83983 -> Prop) : term22 _83983 a P s.
Proof. exact (@lem4868570 _83983 a P s). Qed.
Lemma lem4868572 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term22 _83983 a P s) = ((term23 _83983 a s P) = (term24 _83983 a s P)).
Proof. exact (eq_refl (term22 _83983 a P s)). Qed.
Lemma lem4868577 {_111767 : Type'} (P : type686 _111767) (s : _111767 -> Prop) : (@UNION_OF _111767 (@ARBITRARY _111767) P s) = ((@UNION_OF _111767 (@ARBITRARY _111767) P s) = True).
Proof. exact (@lem7 (@UNION_OF _111767 (@ARBITRARY _111767) P s)). Qed.
Lemma lem4868579 {_111767 : Type'} (P : type686 _111767) (t : _111767 -> Prop) : (@UNION_OF _111767 (@ARBITRARY _111767) P t) = ((@UNION_OF _111767 (@ARBITRARY _111767) P t) = True).
Proof. exact (@lem7 (@UNION_OF _111767 (@ARBITRARY _111767) P t)). Qed.
Lemma lem4868582 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term23 _83983 a s P) = (term24 _83983 a s P).
Proof. exact (EQ_MP (@lem4868572 _83983 a s P) (@lem4868571 _83983 a P s)). Qed.
Lemma lem4868583 {_111767 : Type'} (a : _111767 -> Prop) (s : type686 _111767) (P : type686 _111767) : (term25 _111767 a s P) = (term26 _111767 a s P).
Proof. exact (@lem4868582 (_111767 -> Prop) a s P). Qed.
Lemma lem4868584 {_111767 : Type'} (s : _111767 -> Prop) (t : _111767 -> Prop) (P : type686 _111767) : (term27 _111767 s t P) = (term28 _111767 s t P).
Proof. exact (@lem4868583 _111767 s (@INSERT (_111767 -> Prop) t (@EMPTY (_111767 -> Prop))) (term29 _111767 P)). Qed.
Lemma lem4868585 {_111767 : Type'} (P : type686 _111767) (s' : _111767 -> Prop) : (term30 _111767 P s') = (@UNION_OF _111767 (@ARBITRARY _111767) P s').
Proof. exact (eq_refl (term30 _111767 P s')). Qed.
Lemma lem4868586 {_111767 : Type'} (s' : _111767 -> Prop) (s : _111767 -> Prop) (t : _111767 -> Prop) : (term31 _111767 s' s t) = (term31 _111767 s' s t).
Proof. exact (eq_refl (term31 _111767 s' s t)). Qed.
Lemma lem4868587 {_111767 : Type'} (s : _111767 -> Prop) (t : _111767 -> Prop) (P : type686 _111767) (s' : _111767 -> Prop) : (term32 _111767 s t P s') = (term33 _111767 s t P s').
Proof. exact (MK_COMB (@lem4868586 _111767 s' s t) (@lem4868585 _111767 P s')). Qed.
Lemma lem4868588 {_111767 : Type'} (s : _111767 -> Prop) (t : _111767 -> Prop) (P : type686 _111767) : (term34 _111767 s t P) = (term35 _111767 s t P).
Proof. exact (fun_ext (fun s' : _111767 -> Prop => @lem4868587 _111767 s t P s')). Qed.
Lemma lem4868589 {_111767 : Type'} : (@all (_111767 -> Prop)) = (@all (_111767 -> Prop)).
Proof. exact (eq_refl (@all (_111767 -> Prop))). Qed.
Lemma lem4868590 {_111767 : Type'} (s : _111767 -> Prop) (t : _111767 -> Prop) (P : type686 _111767) : (term27 _111767 s t P) = (term36 _111767 s t P).
Proof. exact (MK_COMB (@lem4868589 _111767) (@lem4868588 _111767 s t P)). Qed.
Lemma lem4868591 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4868592 {_111767 : Type'} (s : _111767 -> Prop) (t : _111767 -> Prop) (P : type686 _111767) : (term37 _111767 s t P) = (term38 _111767 s t P).
Proof. exact (MK_COMB (@lem4868591) (@lem4868590 _111767 s t P)). Qed.
Lemma lem4868593 {_111767 : Type'} (P : type686 _111767) (s : _111767 -> Prop) : (term30 _111767 P s) = (@UNION_OF _111767 (@ARBITRARY _111767) P s).
Proof. exact (eq_refl (term30 _111767 P s)). Qed.
Lemma lem4868594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4868595 {_111767 : Type'} (P : type686 _111767) (s : _111767 -> Prop) : (term39 _111767 P s) = (term40 _111767 P s).
Proof. exact (MK_COMB (@lem4868594) (@lem4868593 _111767 P s)). Qed.
Lemma lem4868596 {_111767 : Type'} (P : type686 _111767) (s' : _111767 -> Prop) : (term30 _111767 P s') = (@UNION_OF _111767 (@ARBITRARY _111767) P s').
Proof. exact (eq_refl (term30 _111767 P s')). Qed.
Lemma lem4868597 {_111767 : Type'} (s' : _111767 -> Prop) (t : _111767 -> Prop) : (term41 _111767 s' t) = (term41 _111767 s' t).
Proof. exact (eq_refl (term41 _111767 s' t)). Qed.
Lemma lem4868598 {_111767 : Type'} (t : _111767 -> Prop) (P : type686 _111767) (s' : _111767 -> Prop) : (term42 _111767 t P s') = (term43 _111767 t P s').
Proof. exact (MK_COMB (@lem4868597 _111767 s' t) (@lem4868596 _111767 P s')). Qed.
Lemma lem4868599 {_111767 : Type'} (t : _111767 -> Prop) (P : type686 _111767) : (term44 _111767 t P) = (term45 _111767 t P).
Proof. exact (fun_ext (fun s' : _111767 -> Prop => @lem4868598 _111767 t P s')). Qed.
Lemma lem4868600 {_111767 : Type'} : (@all (_111767 -> Prop)) = (@all (_111767 -> Prop)).
Proof. exact (eq_refl (@all (_111767 -> Prop))). Qed.
Lemma lem4868601 {_111767 : Type'} (t : _111767 -> Prop) (P : type686 _111767) : (term46 _111767 t P) = (term47 _111767 t P).
Proof. exact (MK_COMB (@lem4868600 _111767) (@lem4868599 _111767 t P)). Qed.
Lemma lem4868602 {_111767 : Type'} (s : _111767 -> Prop) (t : _111767 -> Prop) (P : type686 _111767) : (term28 _111767 s t P) = (term48 _111767 s t P).
Proof. exact (MK_COMB (@lem4868595 _111767 P s) (@lem4868601 _111767 t P)). Qed.
Lemma lem4868603 {_111767 : Type'} (s : _111767 -> Prop) (t : _111767 -> Prop) (P : type686 _111767) : ((term27 _111767 s t P) = (term28 _111767 s t P)) = ((term36 _111767 s t P) = (term48 _111767 s t P)).
Proof. exact (MK_COMB (@lem4868592 _111767 s t P) (@lem4868602 _111767 s t P)). Qed.
Lemma lem4868604 {_111767 : Type'} (s : _111767 -> Prop) (t : _111767 -> Prop) (P : type686 _111767) : (term36 _111767 s t P) = (term48 _111767 s t P).
Proof. exact (EQ_MP (@lem4868603 _111767 s t P) (@lem4868584 _111767 s t P)). Qed.
Lemma lem4868608 {_111767 : Type'} (P : type686 _111767) (s : _111767 -> Prop) (h1 : @UNION_OF _111767 (@ARBITRARY _111767) P s) : (@UNION_OF _111767 (@ARBITRARY _111767) P s) = True.
Proof. exact (EQ_MP (@lem4868577 _111767 P s) (@lem4868554 _111767 P s h1)). Qed.
Lemma lem4868609 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4868610 {_111767 : Type'} (P : type686 _111767) (s : _111767 -> Prop) (h1 : @UNION_OF _111767 (@ARBITRARY _111767) P s) : (term40 _111767 P s) = (and True).
Proof. exact (MK_COMB (@lem4868609) (@lem4868608 _111767 P s h1)). Qed.
Lemma lem4868612 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term23 _83983 a s P) = (term24 _83983 a s P).
Proof. exact (EQ_MP (@lem4868572 _83983 a s P) (@lem4868571 _83983 a P s)). Qed.
Lemma lem4868613 {_111767 : Type'} (a : _111767 -> Prop) (s : type686 _111767) (P : type686 _111767) : (term25 _111767 a s P) = (term26 _111767 a s P).
Proof. exact (@lem4868612 (_111767 -> Prop) a s P). Qed.
Lemma lem4868614 {_111767 : Type'} (t : _111767 -> Prop) (P : type686 _111767) : (term46 _111767 t P) = (term49 _111767 t P).
Proof. exact (@lem4868613 _111767 t (@EMPTY (_111767 -> Prop)) (term29 _111767 P)). Qed.
Lemma lem4868615 {_111767 : Type'} (P : type686 _111767) (s' : _111767 -> Prop) : (term30 _111767 P s') = (@UNION_OF _111767 (@ARBITRARY _111767) P s').
Proof. exact (eq_refl (term30 _111767 P s')). Qed.
Lemma lem4868616 {_111767 : Type'} (s' : _111767 -> Prop) (t : _111767 -> Prop) : (term41 _111767 s' t) = (term41 _111767 s' t).
Proof. exact (eq_refl (term41 _111767 s' t)). Qed.
Lemma lem4868617 {_111767 : Type'} (t : _111767 -> Prop) (P : type686 _111767) (s' : _111767 -> Prop) : (term42 _111767 t P s') = (term43 _111767 t P s').
Proof. exact (MK_COMB (@lem4868616 _111767 s' t) (@lem4868615 _111767 P s')). Qed.
Lemma lem4868618 {_111767 : Type'} (t : _111767 -> Prop) (P : type686 _111767) : (term44 _111767 t P) = (term45 _111767 t P).
Proof. exact (fun_ext (fun s' : _111767 -> Prop => @lem4868617 _111767 t P s')). Qed.
Lemma lem4868619 {_111767 : Type'} : (@all (_111767 -> Prop)) = (@all (_111767 -> Prop)).
Proof. exact (eq_refl (@all (_111767 -> Prop))). Qed.
Lemma lem4868620 {_111767 : Type'} (t : _111767 -> Prop) (P : type686 _111767) : (term46 _111767 t P) = (term47 _111767 t P).
Proof. exact (MK_COMB (@lem4868619 _111767) (@lem4868618 _111767 t P)). Qed.
Lemma lem4868621 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4868622 {_111767 : Type'} (t : _111767 -> Prop) (P : type686 _111767) : (term50 _111767 t P) = (term51 _111767 t P).
Proof. exact (MK_COMB (@lem4868621) (@lem4868620 _111767 t P)). Qed.
Lemma lem4868623 {_111767 : Type'} (P : type686 _111767) (t : _111767 -> Prop) : (term30 _111767 P t) = (@UNION_OF _111767 (@ARBITRARY _111767) P t).
Proof. exact (eq_refl (term30 _111767 P t)). Qed.
Lemma lem4868624 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4868625 {_111767 : Type'} (P : type686 _111767) (t : _111767 -> Prop) : (term39 _111767 P t) = (term40 _111767 P t).
Proof. exact (MK_COMB (@lem4868624) (@lem4868623 _111767 P t)). Qed.
Lemma lem4868626 {_111767 : Type'} (P : type686 _111767) (s' : _111767 -> Prop) : (term30 _111767 P s') = (@UNION_OF _111767 (@ARBITRARY _111767) P s').
Proof. exact (eq_refl (term30 _111767 P s')). Qed.
Lemma lem4868627 {_111767 : Type'} (s' : _111767 -> Prop) : (term52 _111767 s') = (term52 _111767 s').
Proof. exact (eq_refl (term52 _111767 s')). Qed.
Lemma lem4868628 {_111767 : Type'} (P : type686 _111767) (s' : _111767 -> Prop) : (term53 _111767 P s') = (term54 _111767 P s').
Proof. exact (MK_COMB (@lem4868627 _111767 s') (@lem4868626 _111767 P s')). Qed.
Lemma lem4868629 {_111767 : Type'} (P : type686 _111767) : (term55 _111767 P) = (term56 _111767 P).
Proof. exact (fun_ext (fun s' : _111767 -> Prop => @lem4868628 _111767 P s')). Qed.
Lemma lem4868630 {_111767 : Type'} : (@all (_111767 -> Prop)) = (@all (_111767 -> Prop)).
Proof. exact (eq_refl (@all (_111767 -> Prop))). Qed.
Lemma lem4868631 {_111767 : Type'} (P : type686 _111767) : (term57 _111767 P) = (term58 _111767 P).
Proof. exact (MK_COMB (@lem4868630 _111767) (@lem4868629 _111767 P)). Qed.
Lemma lem4868632 {_111767 : Type'} (t : _111767 -> Prop) (P : type686 _111767) : (term49 _111767 t P) = (term59 _111767 t P).
Proof. exact (MK_COMB (@lem4868625 _111767 P t) (@lem4868631 _111767 P)). Qed.
Lemma lem4868633 {_111767 : Type'} (t : _111767 -> Prop) (P : type686 _111767) : ((term46 _111767 t P) = (term49 _111767 t P)) = ((term47 _111767 t P) = (term59 _111767 t P)).
Proof. exact (MK_COMB (@lem4868622 _111767 t P) (@lem4868632 _111767 t P)). Qed.
Lemma lem4868634 {_111767 : Type'} (t : _111767 -> Prop) (P : type686 _111767) : (term47 _111767 t P) = (term59 _111767 t P).
Proof. exact (EQ_MP (@lem4868633 _111767 t P) (@lem4868614 _111767 t P)). Qed.
Lemma lem4868638 {_111767 : Type'} (P : type686 _111767) (t : _111767 -> Prop) (h1 : @UNION_OF _111767 (@ARBITRARY _111767) P t) : (@UNION_OF _111767 (@ARBITRARY _111767) P t) = True.
Proof. exact (EQ_MP (@lem4868579 _111767 P t) (@lem4868553 _111767 P t h1)). Qed.
Lemma lem4868639 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4868640 {_111767 : Type'} (P : type686 _111767) (t : _111767 -> Prop) (h1 : @UNION_OF _111767 (@ARBITRARY _111767) P t) : (term40 _111767 P t) = (and True).
Proof. exact (MK_COMB (@lem4868639) (@lem4868638 _111767 P t h1)). Qed.
Lemma lem4868647 {_111767 : Type'} (P : type686 _111767) : (term58 _111767 P) = (term58 _111767 P).
Proof. exact (eq_refl (term58 _111767 P)). Qed.
Lemma lem4868648 {_111767 : Type'} (P : type686 _111767) (t : _111767 -> Prop) (h1 : @UNION_OF _111767 (@ARBITRARY _111767) P t) : (term59 _111767 t P) = (term60 _111767 P).
Proof. exact (MK_COMB (@lem4868640 _111767 P t h1) (@lem4868647 _111767 P)). Qed.
Lemma lem4868650 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4868651 {_111767 : Type'} (P : type686 _111767) : (term60 _111767 P) = (term58 _111767 P).
Proof. exact (@lem4868650 (term58 _111767 P)). Qed.
Lemma lem4868658 {_111767 : Type'} (P : type686 _111767) (t : _111767 -> Prop) (h1 : @UNION_OF _111767 (@ARBITRARY _111767) P t) : (term59 _111767 t P) = (term58 _111767 P).
Proof. exact (TRANS (@lem4868648 _111767 P t h1) (@lem4868651 _111767 P)). Qed.
Lemma lem4868659 {_111767 : Type'} (P : type686 _111767) (t : _111767 -> Prop) (h1 : @UNION_OF _111767 (@ARBITRARY _111767) P t) : (term47 _111767 t P) = (term58 _111767 P).
Proof. exact (TRANS (@lem4868634 _111767 t P) (@lem4868658 _111767 P t h1)). Qed.
Lemma lem4868660 {_111767 : Type'} (s : _111767 -> Prop) (P : type686 _111767) (t : _111767 -> Prop) (h1 : @UNION_OF _111767 (@ARBITRARY _111767) P s) (h2 : @UNION_OF _111767 (@ARBITRARY _111767) P t) : (term48 _111767 s t P) = (term60 _111767 P).
Proof. exact (MK_COMB (@lem4868610 _111767 P s h1) (@lem4868659 _111767 P t h2)). Qed.
Lemma lem4868662 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4868663 {_111767 : Type'} (P : type686 _111767) : (term60 _111767 P) = (term58 _111767 P).
Proof. exact (@lem4868662 (term58 _111767 P)). Qed.
Lemma lem4868670 {_111767 : Type'} (s : _111767 -> Prop) (P : type686 _111767) (t : _111767 -> Prop) (h1 : @UNION_OF _111767 (@ARBITRARY _111767) P s) (h2 : @UNION_OF _111767 (@ARBITRARY _111767) P t) : (term48 _111767 s t P) = (term58 _111767 P).
Proof. exact (TRANS (@lem4868660 _111767 s P t h1 h2) (@lem4868663 _111767 P)). Qed.
Lemma lem4868671 {_111767 : Type'} (s : _111767 -> Prop) (P : type686 _111767) (t : _111767 -> Prop) (h1 : @UNION_OF _111767 (@ARBITRARY _111767) P s) (h2 : @UNION_OF _111767 (@ARBITRARY _111767) P t) : (term36 _111767 s t P) = (term58 _111767 P).
Proof. exact (TRANS (@lem4868604 _111767 s t P) (@lem4868670 _111767 s P t h1 h2)). Qed.
Lemma lem4868672 {_111767 : Type'} (s : _111767 -> Prop) (P : type686 _111767) (t : _111767 -> Prop) (h1 : @UNION_OF _111767 (@ARBITRARY _111767) P s) (h2 : @UNION_OF _111767 (@ARBITRARY _111767) P t) : (term58 _111767 P) = (term36 _111767 s t P).
Proof. exact (SYM (@lem4868671 _111767 s P t h1 h2)). Qed.
Lemma lem4868680 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4868518 A x (@lem4868517 A x)). Qed.
Lemma lem4868681 {_111767 : Type'} (x : _111767 -> Prop) : (@IN (_111767 -> Prop) x (@EMPTY (_111767 -> Prop))) = False.
Proof. exact (@lem4868680 (_111767 -> Prop) x). Qed.
Lemma lem4868682 {_111767 : Type'} (s' : _111767 -> Prop) : (@IN (_111767 -> Prop) s' (@EMPTY (_111767 -> Prop))) = False.
Proof. exact (@lem4868681 _111767 s'). Qed.
Lemma lem4868683 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4868684 {_111767 : Type'} (s' : _111767 -> Prop) : (term52 _111767 s') = (imp False).
Proof. exact (MK_COMB (@lem4868683) (@lem4868682 _111767 s')). Qed.
Lemma lem4868685 {_111767 : Type'} (P : type686 _111767) (s' : _111767 -> Prop) : (@UNION_OF _111767 (@ARBITRARY _111767) P s') = (@UNION_OF _111767 (@ARBITRARY _111767) P s').
Proof. exact (eq_refl (@UNION_OF _111767 (@ARBITRARY _111767) P s')). Qed.
Lemma lem4868686 {_111767 : Type'} (P : type686 _111767) (s' : _111767 -> Prop) : (term54 _111767 P s') = (term61 _111767 P s').
Proof. exact (MK_COMB (@lem4868684 _111767 s') (@lem4868685 _111767 P s')). Qed.
Lemma lem4868688 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4868689 {_111767 : Type'} (P : type686 _111767) (s' : _111767 -> Prop) : (term61 _111767 P s') = True.
Proof. exact (@lem4868688 (@UNION_OF _111767 (@ARBITRARY _111767) P s')). Qed.
Lemma lem4868690 {_111767 : Type'} (P : type686 _111767) (s' : _111767 -> Prop) : (term54 _111767 P s') = True.
Proof. exact (TRANS (@lem4868686 _111767 P s') (@lem4868689 _111767 P s')). Qed.
Lemma lem4868691 {_111767 : Type'} (P : type686 _111767) : (term56 _111767 P) = (term62 _111767).
Proof. exact (fun_ext (fun s' : _111767 -> Prop => @lem4868690 _111767 P s')). Qed.
Lemma lem4868692 {_111767 : Type'} : (@all (_111767 -> Prop)) = (@all (_111767 -> Prop)).
Proof. exact (eq_refl (@all (_111767 -> Prop))). Qed.
Lemma lem4868693 {_111767 : Type'} (P : type686 _111767) : (term58 _111767 P) = (term63 _111767).
Proof. exact (MK_COMB (@lem4868692 _111767) (@lem4868691 _111767 P)). Qed.
Lemma lem4868695 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4868696 {_111767 : Type'} (t : Prop) : (term65 _111767 t) = t.
Proof. exact (@lem4868695 (_111767 -> Prop) t). Qed.
Lemma lem4868697 {_111767 : Type'} : (term63 _111767) = True.
Proof. exact (@lem4868696 _111767 True). Qed.
Lemma lem4868698 {_111767 : Type'} (P : type686 _111767) : (term58 _111767 P) = True.
Proof. exact (TRANS (@lem4868693 _111767 P) (@lem4868697 _111767)). Qed.
Lemma lem4868699 {_111767 : Type'} (P : type686 _111767) : True = (term58 _111767 P).
Proof. exact (SYM (@lem4868698 _111767 P)). Qed.
Lemma lem4868700 {_111767 : Type'} (P : type686 _111767) : term58 _111767 P.
Proof. exact (EQ_MP (@lem4868699 _111767 P) (@lem0)). Qed.
Lemma lem4868701 {_111767 : Type'} (s : _111767 -> Prop) (P : type686 _111767) (t : _111767 -> Prop) (h1 : @UNION_OF _111767 (@ARBITRARY _111767) P s) (h2 : @UNION_OF _111767 (@ARBITRARY _111767) P t) : term36 _111767 s t P.
Proof. exact (EQ_MP (@lem4868672 _111767 s P t h1 h2) (@lem4868700 _111767 P)). Qed.
Lemma lem4868702 {_111767 : Type'} (s : _111767 -> Prop) (P : type686 _111767) (t : _111767 -> Prop) (h1 : @UNION_OF _111767 (@ARBITRARY _111767) P s) (h2 : @UNION_OF _111767 (@ARBITRARY _111767) P t) : term15 _111767 P s t.
Proof. exact (@lem4868564 _111767 P s t (@lem4868701 _111767 s P t h1 h2)). Qed.
Lemma lem4868703 {_111767 : Type'} (s : _111767 -> Prop) (P : type686 _111767) (t : _111767 -> Prop) (h1 : @UNION_OF _111767 (@ARBITRARY _111767) P s) (h2 : @UNION_OF _111767 (@ARBITRARY _111767) P t) : term14 _111767 P s t.
Proof. exact (EQ_MP (@lem4868560 _111767 P s t) (@lem4868702 _111767 s P t h1 h2)). Qed.
Lemma lem4868704 {_111767 : Type'} (s : _111767 -> Prop) (P : type686 _111767) (t : _111767 -> Prop) (h1 : term13 _111767 s P t) : @UNION_OF _111767 (@ARBITRARY _111767) P t.
Proof. exact (proj2 (@lem4868552 _111767 s P t h1)). Qed.
Lemma lem4868705 {_111767 : Type'} (s : _111767 -> Prop) (P : type686 _111767) (t : _111767 -> Prop) (h1 : term13 _111767 s P t) : @UNION_OF _111767 (@ARBITRARY _111767) P s.
Proof. exact (proj1 (@lem4868552 _111767 s P t h1)). Qed.
Lemma lem4868706 {_111767 : Type'} (s : _111767 -> Prop) (P : type686 _111767) (t : _111767 -> Prop) (h1 : @UNION_OF _111767 (@ARBITRARY _111767) P s) (h2 : @UNION_OF _111767 (@ARBITRARY _111767) P t) : (@UNION_OF _111767 (@ARBITRARY _111767) P t) = (term14 _111767 P s t).
Proof. exact (prop_ext (fun h3 : @UNION_OF _111767 (@ARBITRARY _111767) P t => @lem4868703 _111767 s P t h1 h2) (fun h3 : term14 _111767 P s t => @lem4868553 _111767 P t h2)). Qed.
Lemma lem4868707 {_111767 : Type'} (s : _111767 -> Prop) (P : type686 _111767) (t : _111767 -> Prop) (h1 : @UNION_OF _111767 (@ARBITRARY _111767) P s) (h2 : @UNION_OF _111767 (@ARBITRARY _111767) P t) : term14 _111767 P s t.
Proof. exact (EQ_MP (@lem4868706 _111767 s P t h1 h2) (@lem4868553 _111767 P t h2)). Qed.
Lemma lem4868708 {_111767 : Type'} (s : _111767 -> Prop) (P : type686 _111767) (t : _111767 -> Prop) (h1 : @UNION_OF _111767 (@ARBITRARY _111767) P s) (h2 : @UNION_OF _111767 (@ARBITRARY _111767) P t) : (@UNION_OF _111767 (@ARBITRARY _111767) P s) = (term14 _111767 P s t).
Proof. exact (prop_ext (fun h3 : @UNION_OF _111767 (@ARBITRARY _111767) P s => @lem4868707 _111767 s P t h1 h2) (fun h3 : term14 _111767 P s t => @lem4868554 _111767 P s h1)). Qed.
Lemma lem4868709 {_111767 : Type'} (s : _111767 -> Prop) (P : type686 _111767) (t : _111767 -> Prop) (h1 : @UNION_OF _111767 (@ARBITRARY _111767) P s) (h2 : @UNION_OF _111767 (@ARBITRARY _111767) P t) : term14 _111767 P s t.
Proof. exact (EQ_MP (@lem4868708 _111767 s P t h1 h2) (@lem4868554 _111767 P s h1)). Qed.
Lemma lem4868710 {_111767 : Type'} (t : _111767 -> Prop) (P : type686 _111767) (s : _111767 -> Prop) (h1 : term13 _111767 s P t) (h2 : @UNION_OF _111767 (@ARBITRARY _111767) P s) : (@UNION_OF _111767 (@ARBITRARY _111767) P t) = (term14 _111767 P s t).
Proof. exact (prop_ext (fun h3 : @UNION_OF _111767 (@ARBITRARY _111767) P t => @lem4868709 _111767 s P t h2 h3) (fun h3 : term14 _111767 P s t => @lem4868704 _111767 s P t h1)). Qed.
Lemma lem4868711 {_111767 : Type'} (t : _111767 -> Prop) (P : type686 _111767) (s : _111767 -> Prop) (h1 : term13 _111767 s P t) (h2 : @UNION_OF _111767 (@ARBITRARY _111767) P s) : term14 _111767 P s t.
Proof. exact (EQ_MP (@lem4868710 _111767 t P s h1 h2) (@lem4868704 _111767 s P t h1)). Qed.
Lemma lem4868712 {_111767 : Type'} (s : _111767 -> Prop) (P : type686 _111767) (t : _111767 -> Prop) (h1 : term13 _111767 s P t) : (@UNION_OF _111767 (@ARBITRARY _111767) P s) = (term14 _111767 P s t).
Proof. exact (prop_ext (fun h2 : @UNION_OF _111767 (@ARBITRARY _111767) P s => @lem4868711 _111767 t P s h1 h2) (fun h2 : term14 _111767 P s t => @lem4868705 _111767 s P t h1)). Qed.
Lemma lem4868713 {_111767 : Type'} (s : _111767 -> Prop) (P : type686 _111767) (t : _111767 -> Prop) (h1 : term13 _111767 s P t) : term14 _111767 P s t.
Proof. exact (EQ_MP (@lem4868712 _111767 s P t h1) (@lem4868705 _111767 s P t h1)). Qed.
Lemma lem4868714 {_111767 : Type'} (P : type686 _111767) (s : _111767 -> Prop) (t : _111767 -> Prop) : term66 _111767 P s t.
Proof. exact (fun h0 : term13 _111767 s P t => @lem4868713 _111767 s P t h0). Qed.
Lemma lem4868719 {_111767 : Type'} (P : type686 _111767) (s : _111767 -> Prop) : term67 _111767 P s.
Proof. exact (fun t : _111767 -> Prop => @lem4868714 _111767 P s t). Qed.
Lemma lem4868724 {_111767 : Type'} (P : type686 _111767) : term68 _111767 P.
Proof. exact (fun s : _111767 -> Prop => @lem4868719 _111767 P s). Qed.
Lemma lem4868729 {_111767 : Type'} : term69 _111767.
Proof. exact (fun P : type686 _111767 => @lem4868724 _111767 P). Qed.
