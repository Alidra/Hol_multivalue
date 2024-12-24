Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_IN_IMAGE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import IN_IMAGE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem3385501 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3385502 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3385503 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3385502 t1) (@lem3385501 t1)). Qed.
Lemma lem3385504 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3385503 t1 t2). Qed.
Lemma lem3385505 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3385506 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3385505 t1 t2) (@lem3385504 t1 t2)). Qed.
Lemma lem3385507 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3385506 t1 t2 t3). Qed.
Lemma lem3385508 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3385509 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3385508 t1 t2 t3) (@lem3385507 t1 t2 t3)). Qed.
Lemma lem3385510 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3385509 t1 t2 t3)). Qed.
Lemma lem3385511 {A B : Type'} (y : B) : term7 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem3385512 {A B : Type'} (y : B) : (term7 A B y) = (term8 A B y).
Proof. exact (eq_refl (term7 A B y)). Qed.
Lemma lem3385513 {A B : Type'} (y : B) : term8 A B y.
Proof. exact (EQ_MP (@lem3385512 A B y) (@lem3385511 A B y)). Qed.
Lemma lem3385514 {A B : Type'} (y : B) (s : A -> Prop) : term9 A B y s.
Proof. exact (@lem3385513 A B y s). Qed.
Lemma lem3385515 {A B : Type'} (y : B) (s : A -> Prop) : (term9 A B y s) = (term10 A B y s).
Proof. exact (eq_refl (term9 A B y s)). Qed.
Lemma lem3385516 {A B : Type'} (y : B) (s : A -> Prop) : term10 A B y s.
Proof. exact (EQ_MP (@lem3385515 A B y s) (@lem3385514 A B y s)). Qed.
Lemma lem3385517 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term11 A B y s f.
Proof. exact (@lem3385516 A B y s f). Qed.
Lemma lem3385518 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term11 A B y s f) = ((term12 A B y f s) = (term13 A B y f s)).
Proof. exact (eq_refl (term11 A B y s f)). Qed.
Lemma lem3385537 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term12 A B y f s) = (term13 A B y f s).
Proof. exact (EQ_MP (@lem3385518 A B y f s) (@lem3385517 A B y s f)). Qed.
Lemma lem3385538 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term14 _87967 _87968 y f s) = (term15 _87967 _87968 y f s).
Proof. exact (@lem3385537 _87968 _87967 y f s). Qed.
Lemma lem3385547 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3385548 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term16 _87967 _87968 y f s) = (term17 _87967 _87968 y f s).
Proof. exact (MK_COMB (@lem3385547) (@lem3385538 _87967 _87968 y f s)). Qed.
Lemma lem3385549 {_87967 : Type'} (P : _87967 -> Prop) (y : _87967) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem3385550 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term18 _87967 _87968 f s P y) = (term19 _87967 _87968 f s P y).
Proof. exact (MK_COMB (@lem3385548 _87967 _87968 y f s) (@lem3385549 _87967 P y)). Qed.
Lemma lem3385553 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term20 _87967 _87968 f s P) = (term21 _87967 _87968 f s P).
Proof. exact (fun_ext (fun y : _87967 => @lem3385550 _87967 _87968 f s P y)). Qed.
Lemma lem3385554 {_87967 : Type'} : (@all _87967) = (@all _87967).
Proof. exact (eq_refl (@all _87967)). Qed.
Lemma lem3385555 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term22 _87967 _87968 f s P) = (term23 _87967 _87968 f s P).
Proof. exact (MK_COMB (@lem3385554 _87967) (@lem3385553 _87967 _87968 f s P)). Qed.
Lemma lem3385560 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3385561 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term24 _87967 _87968 f s P) = (term25 _87967 _87968 f s P).
Proof. exact (MK_COMB (@lem3385560) (@lem3385555 _87967 _87968 f s P)). Qed.
Lemma lem3385568 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term26 _87967 _87968 s P f) = (term26 _87967 _87968 s P f).
Proof. exact (eq_refl (term26 _87967 _87968 s P f)). Qed.
Lemma lem3385569 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : ((term22 _87967 _87968 f s P) = (term26 _87967 _87968 s P f)) = ((term23 _87967 _87968 f s P) = (term26 _87967 _87968 s P f)).
Proof. exact (MK_COMB (@lem3385561 _87967 _87968 f s P) (@lem3385568 _87967 _87968 s P f)). Qed.
Lemma lem3385572 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term27 _87967 _87968 P f) = (term28 _87967 _87968 P f).
Proof. exact (fun_ext (fun s : _87968 -> Prop => @lem3385569 _87967 _87968 s P f)). Qed.
Lemma lem3385573 {_87968 : Type'} : (@all (_87968 -> Prop)) = (@all (_87968 -> Prop)).
Proof. exact (eq_refl (@all (_87968 -> Prop))). Qed.
Lemma lem3385574 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term29 _87967 _87968 P f) = (term30 _87967 _87968 P f).
Proof. exact (MK_COMB (@lem3385573 _87968) (@lem3385572 _87967 _87968 P f)). Qed.
Lemma lem3385579 {_87967 _87968 : Type'} (P : _87967 -> Prop) : (term31 _87967 _87968 P) = (term32 _87967 _87968 P).
Proof. exact (fun_ext (fun f : _87968 -> _87967 => @lem3385574 _87967 _87968 P f)). Qed.
Lemma lem3385580 {_87967 _87968 : Type'} : (@all (_87968 -> _87967)) = (@all (_87968 -> _87967)).
Proof. exact (eq_refl (@all (_87968 -> _87967))). Qed.
Lemma lem3385581 {_87967 _87968 : Type'} (P : _87967 -> Prop) : (term33 _87967 _87968 P) = (term34 _87967 _87968 P).
Proof. exact (MK_COMB (@lem3385580 _87967 _87968) (@lem3385579 _87967 _87968 P)). Qed.
Lemma lem3385586 {_87967 _87968 : Type'} (P : _87967 -> Prop) : (term34 _87967 _87968 P) = (term33 _87967 _87968 P).
Proof. exact (SYM (@lem3385581 _87967 _87968 P)). Qed.
Lemma lem3385588 (p : Prop) : p = (term35 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3385589 {_87967 _87968 : Type'} (P : _87967 -> Prop) : (term34 _87967 _87968 P) = (term36 _87967 _87968 P).
Proof. exact (@lem3385588 (term34 _87967 _87968 P)). Qed.
Lemma lem3385590 {_87967 _87968 : Type'} (P : _87967 -> Prop) : (term36 _87967 _87968 P) = (term34 _87967 _87968 P).
Proof. exact (SYM (@lem3385589 _87967 _87968 P)). Qed.
Lemma lem3385591 {_87967 _87968 : Type'} (P : _87967 -> Prop) (h1 : term37 _87967 _87968 P) : term37 _87967 _87968 P.
Proof. exact (h1). Qed.
Lemma lem3385594 {_87967 _87968 : Type'} (P : _87967 -> Prop) (h1 : term36 _87967 _87968 P) : term36 _87967 _87968 P.
Proof. exact (h1). Qed.
Lemma lem3385595 {_87967 _87968 : Type'} (P : _87967 -> Prop) : term38 _87967 _87968 P.
Proof. exact (fun h0 : term36 _87967 _87968 P => @lem3385594 _87967 _87968 P h0). Qed.
Lemma lem3385596 {_87967 _87968 : Type'} (P : _87967 -> Prop) (h1 : term38 _87967 _87968 P) : term38 _87967 _87968 P.
Proof. exact (h1). Qed.
Lemma lem3385597 {_87967 _87968 : Type'} (P : _87967 -> Prop) (h1 : term36 _87967 _87968 P) : term36 _87967 _87968 P.
Proof. exact (h1). Qed.
Lemma lem3385598 {_87967 _87968 : Type'} (P : _87967 -> Prop) (h1 : term36 _87967 _87968 P) (h2 : term38 _87967 _87968 P) : term36 _87967 _87968 P.
Proof. exact (@lem3385596 _87967 _87968 P h2 (@lem3385597 _87967 _87968 P h1)). Qed.
Lemma lem3385599 {_87967 _87968 : Type'} (P : _87967 -> Prop) (h1 : term36 _87967 _87968 P) : term39 _87967 _87968 P.
Proof. exact (fun h0 : term38 _87967 _87968 P => @lem3385598 _87967 _87968 P h1 h0). Qed.
Lemma lem3385600 {_87967 _87968 : Type'} (P : _87967 -> Prop) (h1 : term38 _87967 _87968 P) : term38 _87967 _87968 P.
Proof. exact (h1). Qed.
Lemma lem3385601 {_87967 _87968 : Type'} (P : _87967 -> Prop) (h1 : term36 _87967 _87968 P) (h2 : term38 _87967 _87968 P) : term36 _87967 _87968 P.
Proof. exact (@lem3385599 _87967 _87968 P h1 (@lem3385600 _87967 _87968 P h2)). Qed.
Lemma lem3385602 {_87967 _87968 : Type'} (P : _87967 -> Prop) (h1 : term38 _87967 _87968 P) : term38 _87967 _87968 P.
Proof. exact (fun h0 : term36 _87967 _87968 P => @lem3385601 _87967 _87968 P h0 h1). Qed.
Lemma lem3385603 {_87967 _87968 : Type'} (P : _87967 -> Prop) : term40 _87967 _87968 P.
Proof. exact (fun h0 : term38 _87967 _87968 P => @lem3385602 _87967 _87968 P h0). Qed.
Lemma lem3385606 {_87967 _87968 : Type'} (P : _87967 -> Prop) : term38 _87967 _87968 P.
Proof. exact (@lem3385603 _87967 _87968 P (@lem3385595 _87967 _87968 P)). Qed.
Lemma lem3385607 {_87967 _87968 : Type'} (P : _87967 -> Prop) : term38 _87967 _87968 P.
Proof. exact (@lem3385606 _87967 _87968 P). Qed.
Lemma lem3385613 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3385614 {_87967 _87968 : Type'} (P : _87967 -> Prop) : (term36 _87967 _87968 P) = (term41 _87967 _87968 P).
Proof. exact (@lem3385613 (term37 _87967 _87968 P)). Qed.
Lemma lem3385616 (t : Prop) : (term42 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3385617 {_87967 _87968 : Type'} (P : _87967 -> Prop) : (term41 _87967 _87968 P) = (term34 _87967 _87968 P).
Proof. exact (@lem3385616 (term34 _87967 _87968 P)). Qed.
Lemma lem3385622 {_87967 _87968 : Type'} (P : _87967 -> Prop) : (term36 _87967 _87968 P) = (term34 _87967 _87968 P).
Proof. exact (TRANS (@lem3385614 _87967 _87968 P) (@lem3385617 _87967 _87968 P)). Qed.
Lemma lem3385689 {_87967 _87968 : Type'} : (term43 _87967 _87968) = (term44 _87967 _87968).
Proof. exact (fun_ext (fun P : _87967 -> Prop => @lem3385622 _87967 _87968 P)). Qed.
Lemma lem3385690 {_87967 : Type'} : (@all (_87967 -> Prop)) = (@all (_87967 -> Prop)).
Proof. exact (eq_refl (@all (_87967 -> Prop))). Qed.
Lemma lem3385699 {_87967 _87968 : Type'} : (term45 _87967 _87968) = (term46 _87967 _87968).
Proof. exact (MK_COMB (@lem3385690 _87967) (@lem3385689 _87967 _87968)). Qed.
Lemma lem3385704 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term47 _87967 _87968 s P f x) = (term47 _87967 _87968 s P f x).
Proof. exact (eq_refl (term47 _87967 _87968 s P f x)). Qed.
Lemma lem3385705 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term48 _87967 _87968 s P f) = (term48 _87967 _87968 s P f).
Proof. exact (fun_ext (fun x : _87968 => @lem3385704 _87967 _87968 s P f x)). Qed.
Lemma lem3385706 {_87968 : Type'} : (@all _87968) = (@all _87968).
Proof. exact (eq_refl (@all _87968)). Qed.
Lemma lem3385707 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term26 _87967 _87968 s P f) = (term26 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3385706 _87968) (@lem3385705 _87967 _87968 s P f)). Qed.
Lemma lem3385708 {_87967 : Type'} (P : _87967 -> Prop) (y : _87967) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem3385713 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (x : _87968) (s : _87968 -> Prop) : (term49 _87967 _87968 y f x s) = (term49 _87967 _87968 y f x s).
Proof. exact (eq_refl (term49 _87967 _87968 y f x s)). Qed.
Lemma lem3385714 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term50 _87967 _87968 y f s) = (term50 _87967 _87968 y f s).
Proof. exact (fun_ext (fun x : _87968 => @lem3385713 _87967 _87968 y f x s)). Qed.
Lemma lem3385715 {_87968 : Type'} : (@ex _87968) = (@ex _87968).
Proof. exact (eq_refl (@ex _87968)). Qed.
Lemma lem3385716 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term15 _87967 _87968 y f s) = (term15 _87967 _87968 y f s).
Proof. exact (MK_COMB (@lem3385715 _87968) (@lem3385714 _87967 _87968 y f s)). Qed.
Lemma lem3385717 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3385718 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term17 _87967 _87968 y f s) = (term17 _87967 _87968 y f s).
Proof. exact (MK_COMB (@lem3385717) (@lem3385716 _87967 _87968 y f s)). Qed.
Lemma lem3385719 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term19 _87967 _87968 f s P y) = (term19 _87967 _87968 f s P y).
Proof. exact (MK_COMB (@lem3385718 _87967 _87968 y f s) (@lem3385708 _87967 P y)). Qed.
Lemma lem3385720 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term21 _87967 _87968 f s P) = (term21 _87967 _87968 f s P).
Proof. exact (fun_ext (fun y : _87967 => @lem3385719 _87967 _87968 f s P y)). Qed.
Lemma lem3385721 {_87967 : Type'} : (@all _87967) = (@all _87967).
Proof. exact (eq_refl (@all _87967)). Qed.
Lemma lem3385722 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term23 _87967 _87968 f s P) = (term23 _87967 _87968 f s P).
Proof. exact (MK_COMB (@lem3385721 _87967) (@lem3385720 _87967 _87968 f s P)). Qed.
Lemma lem3385723 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3385724 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term25 _87967 _87968 f s P) = (term25 _87967 _87968 f s P).
Proof. exact (MK_COMB (@lem3385723) (@lem3385722 _87967 _87968 f s P)). Qed.
Lemma lem3385725 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : ((term23 _87967 _87968 f s P) = (term26 _87967 _87968 s P f)) = ((term23 _87967 _87968 f s P) = (term26 _87967 _87968 s P f)).
Proof. exact (MK_COMB (@lem3385724 _87967 _87968 f s P) (@lem3385707 _87967 _87968 s P f)). Qed.
Lemma lem3385726 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term28 _87967 _87968 P f) = (term28 _87967 _87968 P f).
Proof. exact (fun_ext (fun s : _87968 -> Prop => @lem3385725 _87967 _87968 s P f)). Qed.
Lemma lem3385727 {_87968 : Type'} : (@all (_87968 -> Prop)) = (@all (_87968 -> Prop)).
Proof. exact (eq_refl (@all (_87968 -> Prop))). Qed.
Lemma lem3385728 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term30 _87967 _87968 P f) = (term30 _87967 _87968 P f).
Proof. exact (MK_COMB (@lem3385727 _87968) (@lem3385726 _87967 _87968 P f)). Qed.
Lemma lem3385729 {_87967 _87968 : Type'} (P : _87967 -> Prop) : (term32 _87967 _87968 P) = (term32 _87967 _87968 P).
Proof. exact (fun_ext (fun f : _87968 -> _87967 => @lem3385728 _87967 _87968 P f)). Qed.
Lemma lem3385730 {_87967 _87968 : Type'} : (@all (_87968 -> _87967)) = (@all (_87968 -> _87967)).
Proof. exact (eq_refl (@all (_87968 -> _87967))). Qed.
Lemma lem3385731 {_87967 _87968 : Type'} (P : _87967 -> Prop) : (term34 _87967 _87968 P) = (term34 _87967 _87968 P).
Proof. exact (MK_COMB (@lem3385730 _87967 _87968) (@lem3385729 _87967 _87968 P)). Qed.
Lemma lem3385732 {_87967 _87968 : Type'} : (term44 _87967 _87968) = (term44 _87967 _87968).
Proof. exact (fun_ext (fun P : _87967 -> Prop => @lem3385731 _87967 _87968 P)). Qed.
Lemma lem3385733 {_87967 : Type'} : (@all (_87967 -> Prop)) = (@all (_87967 -> Prop)).
Proof. exact (eq_refl (@all (_87967 -> Prop))). Qed.
Lemma lem3385734 {_87967 _87968 : Type'} : (term46 _87967 _87968) = (term46 _87967 _87968).
Proof. exact (MK_COMB (@lem3385733 _87967) (@lem3385732 _87967 _87968)). Qed.
Lemma lem3385779 {_87967 _87968 : Type'} : (term45 _87967 _87968) = (term46 _87967 _87968).
Proof. exact (TRANS (@lem3385699 _87967 _87968) (@lem3385734 _87967 _87968)). Qed.
Lemma lem3385780 {_87967 _87968 : Type'} : (term46 _87967 _87968) = (term45 _87967 _87968).
Proof. exact (SYM (@lem3385779 _87967 _87968)). Qed.
Lemma lem3385782 (p : Prop) : p = (term35 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3385783 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : ((term23 _87967 _87968 f s P) = (term26 _87967 _87968 s P f)) = (term51 _87967 _87968 s P f).
Proof. exact (@lem3385782 ((term23 _87967 _87968 f s P) = (term26 _87967 _87968 s P f))). Qed.
Lemma lem3385784 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term51 _87967 _87968 s P f) = ((term23 _87967 _87968 f s P) = (term26 _87967 _87968 s P f)).
Proof. exact (SYM (@lem3385783 _87967 _87968 s P f)). Qed.
Lemma lem3385785 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term52 _87967 _87968 s P f) : term52 _87967 _87968 s P f.
Proof. exact (h1). Qed.
Lemma lem3385794 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (x : _87968) (s : _87968 -> Prop) : (term53 _87967 _87968 y f x s) = (term54 _87967 _87968 y f x s).
Proof. exact (@lem17045 (y = (f x)) (@IN _87968 x s)). Qed.
Lemma lem3385797 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (x : _87968) (s : _87968 -> Prop) : (term49 _87967 _87968 y f x s) = (term49 _87967 _87968 y f x s).
Proof. exact (eq_refl (term49 _87967 _87968 y f x s)). Qed.
Lemma lem3385798 {_87968 : Type'} (P : _87968 -> Prop) : (term55 _87968 P) = (term56 _87968 P).
Proof. exact (@lem18394 _87968 P). Qed.
Lemma lem3385799 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term57 _87967 _87968 y f s) = (term58 _87967 _87968 y f s).
Proof. exact (@lem3385798 _87968 (term50 _87967 _87968 y f s)). Qed.
Lemma lem3385800 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (x : _87968) (s : _87968 -> Prop) : (term59 _87967 _87968 y f s x) = (term49 _87967 _87968 y f x s).
Proof. exact (eq_refl (term59 _87967 _87968 y f s x)). Qed.
Lemma lem3385801 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3385802 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (x : _87968) (s : _87968 -> Prop) : (term60 _87967 _87968 y f s x) = (term53 _87967 _87968 y f x s).
Proof. exact (MK_COMB (@lem3385801) (@lem3385800 _87967 _87968 y f x s)). Qed.
Lemma lem3385803 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (x : _87968) (s : _87968 -> Prop) : (term60 _87967 _87968 y f s x) = (term54 _87967 _87968 y f x s).
Proof. exact (TRANS (@lem3385802 _87967 _87968 y f x s) (@lem3385794 _87967 _87968 y f x s)). Qed.
Lemma lem3385804 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term61 _87967 _87968 y f s) = (term62 _87967 _87968 y f s).
Proof. exact (fun_ext (fun x : _87968 => @lem3385803 _87967 _87968 y f x s)). Qed.
Lemma lem3385805 {_87968 : Type'} : (@all _87968) = (@all _87968).
Proof. exact (eq_refl (@all _87968)). Qed.
Lemma lem3385806 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term58 _87967 _87968 y f s) = (term63 _87967 _87968 y f s).
Proof. exact (MK_COMB (@lem3385805 _87968) (@lem3385804 _87967 _87968 y f s)). Qed.
Lemma lem3385807 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term57 _87967 _87968 y f s) = (term63 _87967 _87968 y f s).
Proof. exact (TRANS (@lem3385799 _87967 _87968 y f s) (@lem3385806 _87967 _87968 y f s)). Qed.
Lemma lem3385808 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term50 _87967 _87968 y f s) = (term50 _87967 _87968 y f s).
Proof. exact (fun_ext (fun x : _87968 => @lem3385797 _87967 _87968 y f x s)). Qed.
Lemma lem3385809 {_87968 : Type'} : (@ex _87968) = (@ex _87968).
Proof. exact (eq_refl (@ex _87968)). Qed.
Lemma lem3385810 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term15 _87967 _87968 y f s) = (term15 _87967 _87968 y f s).
Proof. exact (MK_COMB (@lem3385809 _87968) (@lem3385808 _87967 _87968 y f s)). Qed.
Lemma lem3385811 {_87967 : Type'} (P : _87967 -> Prop) (y : _87967) : (term64 _87967 P y) = (term64 _87967 P y).
Proof. exact (eq_refl (term64 _87967 P y)). Qed.
Lemma lem3385812 {_87967 : Type'} (P : _87967 -> Prop) (y : _87967) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem3385813 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3385814 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term65 _87967 _87968 y f s) = (term65 _87967 _87968 y f s).
Proof. exact (MK_COMB (@lem3385813) (@lem3385810 _87967 _87968 y f s)). Qed.
Lemma lem3385815 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term66 _87967 _87968 f s P y) = (term66 _87967 _87968 f s P y).
Proof. exact (MK_COMB (@lem3385814 _87967 _87968 y f s) (@lem3385811 _87967 P y)). Qed.
Lemma lem3385816 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term67 _87967 _87968 f s P y) = (term66 _87967 _87968 f s P y).
Proof. exact (@lem17362 (term15 _87967 _87968 y f s) (P y)). Qed.
Lemma lem3385817 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term67 _87967 _87968 f s P y) = (term66 _87967 _87968 f s P y).
Proof. exact (TRANS (@lem3385816 _87967 _87968 f s P y) (@lem3385815 _87967 _87968 f s P y)). Qed.
Lemma lem3385818 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3385819 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term68 _87967 _87968 y f s) = (term69 _87967 _87968 y f s).
Proof. exact (MK_COMB (@lem3385818) (@lem3385807 _87967 _87968 y f s)). Qed.
Lemma lem3385820 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term70 _87967 _87968 f s P y) = (term71 _87967 _87968 f s P y).
Proof. exact (MK_COMB (@lem3385819 _87967 _87968 y f s) (@lem3385812 _87967 P y)). Qed.
Lemma lem3385821 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term19 _87967 _87968 f s P y) = (term70 _87967 _87968 f s P y).
Proof. exact (@lem17265 (term15 _87967 _87968 y f s) (P y)). Qed.
Lemma lem3385822 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term19 _87967 _87968 f s P y) = (term71 _87967 _87968 f s P y).
Proof. exact (TRANS (@lem3385821 _87967 _87968 f s P y) (@lem3385820 _87967 _87968 f s P y)). Qed.
Lemma lem3385823 {_87967 : Type'} (P : _87967 -> Prop) : (term72 _87967 P) = (term73 _87967 P).
Proof. exact (@lem18392 _87967 P). Qed.
Lemma lem3385824 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term74 _87967 _87968 f s P) = (term75 _87967 _87968 f s P).
Proof. exact (@lem3385823 _87967 (term21 _87967 _87968 f s P)). Qed.
Lemma lem3385825 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term76 _87967 _87968 f s P y) = (term19 _87967 _87968 f s P y).
Proof. exact (eq_refl (term76 _87967 _87968 f s P y)). Qed.
Lemma lem3385826 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3385827 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term77 _87967 _87968 f s P y) = (term67 _87967 _87968 f s P y).
Proof. exact (MK_COMB (@lem3385826) (@lem3385825 _87967 _87968 f s P y)). Qed.
Lemma lem3385828 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term77 _87967 _87968 f s P y) = (term66 _87967 _87968 f s P y).
Proof. exact (TRANS (@lem3385827 _87967 _87968 f s P y) (@lem3385817 _87967 _87968 f s P y)). Qed.
Lemma lem3385829 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term78 _87967 _87968 f s P) = (term79 _87967 _87968 f s P).
Proof. exact (fun_ext (fun y : _87967 => @lem3385828 _87967 _87968 f s P y)). Qed.
Lemma lem3385830 {_87967 : Type'} : (@ex _87967) = (@ex _87967).
Proof. exact (eq_refl (@ex _87967)). Qed.
Lemma lem3385831 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term75 _87967 _87968 f s P) = (term80 _87967 _87968 f s P).
Proof. exact (MK_COMB (@lem3385830 _87967) (@lem3385829 _87967 _87968 f s P)). Qed.
Lemma lem3385832 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term74 _87967 _87968 f s P) = (term80 _87967 _87968 f s P).
Proof. exact (TRANS (@lem3385824 _87967 _87968 f s P) (@lem3385831 _87967 _87968 f s P)). Qed.
Lemma lem3385833 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term21 _87967 _87968 f s P) = (term81 _87967 _87968 f s P).
Proof. exact (fun_ext (fun y : _87967 => @lem3385822 _87967 _87968 f s P y)). Qed.
Lemma lem3385834 {_87967 : Type'} : (@all _87967) = (@all _87967).
Proof. exact (eq_refl (@all _87967)). Qed.
Lemma lem3385835 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term23 _87967 _87968 f s P) = (term82 _87967 _87968 f s P).
Proof. exact (MK_COMB (@lem3385834 _87967) (@lem3385833 _87967 _87968 f s P)). Qed.
Lemma lem3385844 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term83 _87967 _87968 s P f x) = (term84 _87967 _87968 s P f x).
Proof. exact (@lem17362 (@IN _87968 x s) (term85 _87967 _87968 P f x)). Qed.
Lemma lem3385849 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term47 _87967 _87968 s P f x) = (term86 _87967 _87968 s P f x).
Proof. exact (@lem17265 (@IN _87968 x s) (term85 _87967 _87968 P f x)). Qed.
Lemma lem3385850 {_87968 : Type'} (P : _87968 -> Prop) : (term72 _87968 P) = (term73 _87968 P).
Proof. exact (@lem18392 _87968 P). Qed.
Lemma lem3385851 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term87 _87967 _87968 s P f) = (term88 _87967 _87968 s P f).
Proof. exact (@lem3385850 _87968 (term48 _87967 _87968 s P f)). Qed.
Lemma lem3385852 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term89 _87967 _87968 s P f x) = (term47 _87967 _87968 s P f x).
Proof. exact (eq_refl (term89 _87967 _87968 s P f x)). Qed.
Lemma lem3385853 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3385854 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term90 _87967 _87968 s P f x) = (term83 _87967 _87968 s P f x).
Proof. exact (MK_COMB (@lem3385853) (@lem3385852 _87967 _87968 s P f x)). Qed.
Lemma lem3385855 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term90 _87967 _87968 s P f x) = (term84 _87967 _87968 s P f x).
Proof. exact (TRANS (@lem3385854 _87967 _87968 s P f x) (@lem3385844 _87967 _87968 s P f x)). Qed.
Lemma lem3385856 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term91 _87967 _87968 s P f) = (term92 _87967 _87968 s P f).
Proof. exact (fun_ext (fun x : _87968 => @lem3385855 _87967 _87968 s P f x)). Qed.
Lemma lem3385857 {_87968 : Type'} : (@ex _87968) = (@ex _87968).
Proof. exact (eq_refl (@ex _87968)). Qed.
Lemma lem3385858 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term88 _87967 _87968 s P f) = (term93 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3385857 _87968) (@lem3385856 _87967 _87968 s P f)). Qed.
Lemma lem3385859 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term87 _87967 _87968 s P f) = (term93 _87967 _87968 s P f).
Proof. exact (TRANS (@lem3385851 _87967 _87968 s P f) (@lem3385858 _87967 _87968 s P f)). Qed.
Lemma lem3385860 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term48 _87967 _87968 s P f) = (term94 _87967 _87968 s P f).
Proof. exact (fun_ext (fun x : _87968 => @lem3385849 _87967 _87968 s P f x)). Qed.
Lemma lem3385861 {_87968 : Type'} : (@all _87968) = (@all _87968).
Proof. exact (eq_refl (@all _87968)). Qed.
Lemma lem3385862 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term26 _87967 _87968 s P f) = (term95 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3385861 _87968) (@lem3385860 _87967 _87968 s P f)). Qed.
Lemma lem3385863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3385864 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term96 _87967 _87968 f s P) = (term97 _87967 _87968 f s P).
Proof. exact (MK_COMB (@lem3385863) (@lem3385832 _87967 _87968 f s P)). Qed.
Lemma lem3385865 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term98 _87967 _87968 s P f) = (term99 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3385864 _87967 _87968 f s P) (@lem3385862 _87967 _87968 s P f)). Qed.
Lemma lem3385866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3385867 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term100 _87967 _87968 f s P) = (term101 _87967 _87968 f s P).
Proof. exact (MK_COMB (@lem3385866) (@lem3385835 _87967 _87968 f s P)). Qed.
Lemma lem3385868 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term102 _87967 _87968 s P f) = (term103 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3385867 _87967 _87968 f s P) (@lem3385859 _87967 _87968 s P f)). Qed.
Lemma lem3385869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3385870 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term104 _87967 _87968 s P f) = (term105 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3385869) (@lem3385868 _87967 _87968 s P f)). Qed.
Lemma lem3385871 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term106 _87967 _87968 s P f) = (term107 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3385870 _87967 _87968 s P f) (@lem3385865 _87967 _87968 s P f)). Qed.
Lemma lem3385872 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term52 _87967 _87968 s P f) = (term106 _87967 _87968 s P f).
Proof. exact (@lem17646 (term23 _87967 _87968 f s P) (term26 _87967 _87968 s P f)). Qed.
Lemma lem3385873 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term52 _87967 _87968 s P f) = (term107 _87967 _87968 s P f).
Proof. exact (TRANS (@lem3385872 _87967 _87968 s P f) (@lem3385871 _87967 _87968 s P f)). Qed.
Lemma lem3386148 {A : Type'} (P : Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3386149 {_87968 : Type'} (P : Prop) (Q : _87968 -> Prop) : (term108 _87968 P Q) = (term109 _87968 P Q).
Proof. exact (@lem3386148 _87968 P Q). Qed.
Lemma lem3386150 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term110 _87967 _87968 s P f) = (term111 _87967 _87968 s P f).
Proof. exact (@lem3386149 _87968 (term82 _87967 _87968 f s P) (term92 _87967 _87968 s P f)). Qed.
Lemma lem3386151 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term112 _87967 _87968 s P f x) = (term84 _87967 _87968 s P f x).
Proof. exact (eq_refl (term112 _87967 _87968 s P f x)). Qed.
Lemma lem3386152 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term113 _87967 _87968 s P f) = (term92 _87967 _87968 s P f).
Proof. exact (fun_ext (fun x : _87968 => @lem3386151 _87967 _87968 s P f x)). Qed.
Lemma lem3386153 {_87968 : Type'} : (@ex _87968) = (@ex _87968).
Proof. exact (eq_refl (@ex _87968)). Qed.
Lemma lem3386154 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term114 _87967 _87968 s P f) = (term93 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3386153 _87968) (@lem3386152 _87967 _87968 s P f)). Qed.
Lemma lem3386155 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term101 _87967 _87968 f s P) = (term101 _87967 _87968 f s P).
Proof. exact (eq_refl (term101 _87967 _87968 f s P)). Qed.
Lemma lem3386156 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term110 _87967 _87968 s P f) = (term103 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3386155 _87967 _87968 f s P) (@lem3386154 _87967 _87968 s P f)). Qed.
Lemma lem3386157 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3386158 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term115 _87967 _87968 s P f) = (term116 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3386157) (@lem3386156 _87967 _87968 s P f)). Qed.
Lemma lem3386159 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term112 _87967 _87968 s P f x) = (term84 _87967 _87968 s P f x).
Proof. exact (eq_refl (term112 _87967 _87968 s P f x)). Qed.
Lemma lem3386160 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term101 _87967 _87968 f s P) = (term101 _87967 _87968 f s P).
Proof. exact (eq_refl (term101 _87967 _87968 f s P)). Qed.
Lemma lem3386161 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term117 _87967 _87968 s P f x) = (term118 _87967 _87968 s P f x).
Proof. exact (MK_COMB (@lem3386160 _87967 _87968 f s P) (@lem3386159 _87967 _87968 s P f x)). Qed.
Lemma lem3386162 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term119 _87967 _87968 s P f) = (term120 _87967 _87968 s P f).
Proof. exact (fun_ext (fun x : _87968 => @lem3386161 _87967 _87968 s P f x)). Qed.
Lemma lem3386163 {_87968 : Type'} : (@ex _87968) = (@ex _87968).
Proof. exact (eq_refl (@ex _87968)). Qed.
Lemma lem3386164 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term111 _87967 _87968 s P f) = (term121 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3386163 _87968) (@lem3386162 _87967 _87968 s P f)). Qed.
Lemma lem3386165 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : ((term110 _87967 _87968 s P f) = (term111 _87967 _87968 s P f)) = ((term103 _87967 _87968 s P f) = (term121 _87967 _87968 s P f)).
Proof. exact (MK_COMB (@lem3386158 _87967 _87968 s P f) (@lem3386164 _87967 _87968 s P f)). Qed.
Lemma lem3386166 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term103 _87967 _87968 s P f) = (term121 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem3386165 _87967 _87968 s P f) (@lem3386150 _87967 _87968 s P f)). Qed.
Lemma lem3386167 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3386168 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term105 _87967 _87968 s P f) = (term122 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3386167) (@lem3386166 _87967 _87968 s P f)). Qed.
Lemma lem3386170 {A : Type'} (P : A -> Prop) (Q : Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3386171 {_87968 : Type'} (P : _87968 -> Prop) (Q : Prop) : (term123 _87968 P Q) = (term124 _87968 P Q).
Proof. exact (@lem3386170 _87968 P Q). Qed.
Lemma lem3386172 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term125 _87967 _87968 f s P y) = (term126 _87967 _87968 f s P y).
Proof. exact (@lem3386171 _87968 (term50 _87967 _87968 y f s) (term64 _87967 P y)). Qed.
Lemma lem3386173 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (x : _87968) (s : _87968 -> Prop) : (term59 _87967 _87968 y f s x) = (term49 _87967 _87968 y f x s).
Proof. exact (eq_refl (term59 _87967 _87968 y f s x)). Qed.
Lemma lem3386174 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term127 _87967 _87968 y f s) = (term50 _87967 _87968 y f s).
Proof. exact (fun_ext (fun x : _87968 => @lem3386173 _87967 _87968 y f x s)). Qed.
Lemma lem3386175 {_87968 : Type'} : (@ex _87968) = (@ex _87968).
Proof. exact (eq_refl (@ex _87968)). Qed.
Lemma lem3386176 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term128 _87967 _87968 y f s) = (term15 _87967 _87968 y f s).
Proof. exact (MK_COMB (@lem3386175 _87968) (@lem3386174 _87967 _87968 y f s)). Qed.
Lemma lem3386177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3386178 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term129 _87967 _87968 y f s) = (term65 _87967 _87968 y f s).
Proof. exact (MK_COMB (@lem3386177) (@lem3386176 _87967 _87968 y f s)). Qed.
Lemma lem3386179 {_87967 : Type'} (P : _87967 -> Prop) (y : _87967) : (term64 _87967 P y) = (term64 _87967 P y).
Proof. exact (eq_refl (term64 _87967 P y)). Qed.
Lemma lem3386180 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term125 _87967 _87968 f s P y) = (term66 _87967 _87968 f s P y).
Proof. exact (MK_COMB (@lem3386178 _87967 _87968 y f s) (@lem3386179 _87967 P y)). Qed.
Lemma lem3386181 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3386182 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term130 _87967 _87968 f s P y) = (term131 _87967 _87968 f s P y).
Proof. exact (MK_COMB (@lem3386181) (@lem3386180 _87967 _87968 f s P y)). Qed.
Lemma lem3386183 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (x : _87968) (s : _87968 -> Prop) : (term59 _87967 _87968 y f s x) = (term49 _87967 _87968 y f x s).
Proof. exact (eq_refl (term59 _87967 _87968 y f s x)). Qed.
Lemma lem3386184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3386185 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (x : _87968) (s : _87968 -> Prop) : (term132 _87967 _87968 y f s x) = (term133 _87967 _87968 y f x s).
Proof. exact (MK_COMB (@lem3386184) (@lem3386183 _87967 _87968 y f x s)). Qed.
Lemma lem3386186 {_87967 : Type'} (P : _87967 -> Prop) (y : _87967) : (term64 _87967 P y) = (term64 _87967 P y).
Proof. exact (eq_refl (term64 _87967 P y)). Qed.
Lemma lem3386187 {_87967 _87968 : Type'} (f : _87968 -> _87967) (x : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term134 _87967 _87968 f s x P y) = (term135 _87967 _87968 f x s P y).
Proof. exact (MK_COMB (@lem3386185 _87967 _87968 y f x s) (@lem3386186 _87967 P y)). Qed.
Lemma lem3386188 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term136 _87967 _87968 f s P y) = (term137 _87967 _87968 f s P y).
Proof. exact (fun_ext (fun x : _87968 => @lem3386187 _87967 _87968 f x s P y)). Qed.
Lemma lem3386189 {_87968 : Type'} : (@ex _87968) = (@ex _87968).
Proof. exact (eq_refl (@ex _87968)). Qed.
Lemma lem3386190 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term126 _87967 _87968 f s P y) = (term138 _87967 _87968 f s P y).
Proof. exact (MK_COMB (@lem3386189 _87968) (@lem3386188 _87967 _87968 f s P y)). Qed.
Lemma lem3386191 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : ((term125 _87967 _87968 f s P y) = (term126 _87967 _87968 f s P y)) = ((term66 _87967 _87968 f s P y) = (term138 _87967 _87968 f s P y)).
Proof. exact (MK_COMB (@lem3386182 _87967 _87968 f s P y) (@lem3386190 _87967 _87968 f s P y)). Qed.
Lemma lem3386192 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term66 _87967 _87968 f s P y) = (term138 _87967 _87968 f s P y).
Proof. exact (EQ_MP (@lem3386191 _87967 _87968 f s P y) (@lem3386172 _87967 _87968 f s P y)). Qed.
Lemma lem3386193 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term79 _87967 _87968 f s P) = (term139 _87967 _87968 f s P).
Proof. exact (fun_ext (fun y : _87967 => @lem3386192 _87967 _87968 f s P y)). Qed.
Lemma lem3386194 {_87967 : Type'} : (@ex _87967) = (@ex _87967).
Proof. exact (eq_refl (@ex _87967)). Qed.
Lemma lem3386195 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term80 _87967 _87968 f s P) = (term140 _87967 _87968 f s P).
Proof. exact (MK_COMB (@lem3386194 _87967) (@lem3386193 _87967 _87968 f s P)). Qed.
Lemma lem3386196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3386197 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term97 _87967 _87968 f s P) = (term141 _87967 _87968 f s P).
Proof. exact (MK_COMB (@lem3386196) (@lem3386195 _87967 _87968 f s P)). Qed.
Lemma lem3386198 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term95 _87967 _87968 s P f) = (term95 _87967 _87968 s P f).
Proof. exact (eq_refl (term95 _87967 _87968 s P f)). Qed.
Lemma lem3386199 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term99 _87967 _87968 s P f) = (term142 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3386197 _87967 _87968 f s P) (@lem3386198 _87967 _87968 s P f)). Qed.
Lemma lem3386201 {A : Type'} (P : A -> Prop) (Q : Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3386202 {_87967 : Type'} (P : _87967 -> Prop) (Q : Prop) : (term123 _87967 P Q) = (term124 _87967 P Q).
Proof. exact (@lem3386201 _87967 P Q). Qed.
Lemma lem3386203 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term143 _87967 _87968 s P f) = (term144 _87967 _87968 s P f).
Proof. exact (@lem3386202 _87967 (term139 _87967 _87968 f s P) (term95 _87967 _87968 s P f)). Qed.
Lemma lem3386204 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term145 _87967 _87968 f s P y) = (term138 _87967 _87968 f s P y).
Proof. exact (eq_refl (term145 _87967 _87968 f s P y)). Qed.
Lemma lem3386205 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term146 _87967 _87968 f s P) = (term139 _87967 _87968 f s P).
Proof. exact (fun_ext (fun y : _87967 => @lem3386204 _87967 _87968 f s P y)). Qed.
Lemma lem3386206 {_87967 : Type'} : (@ex _87967) = (@ex _87967).
Proof. exact (eq_refl (@ex _87967)). Qed.
Lemma lem3386207 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term147 _87967 _87968 f s P) = (term140 _87967 _87968 f s P).
Proof. exact (MK_COMB (@lem3386206 _87967) (@lem3386205 _87967 _87968 f s P)). Qed.
Lemma lem3386208 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3386209 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term148 _87967 _87968 f s P) = (term141 _87967 _87968 f s P).
Proof. exact (MK_COMB (@lem3386208) (@lem3386207 _87967 _87968 f s P)). Qed.
Lemma lem3386210 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term95 _87967 _87968 s P f) = (term95 _87967 _87968 s P f).
Proof. exact (eq_refl (term95 _87967 _87968 s P f)). Qed.
Lemma lem3386211 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term143 _87967 _87968 s P f) = (term142 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3386209 _87967 _87968 f s P) (@lem3386210 _87967 _87968 s P f)). Qed.
Lemma lem3386212 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3386213 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term149 _87967 _87968 s P f) = (term150 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3386212) (@lem3386211 _87967 _87968 s P f)). Qed.
Lemma lem3386214 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term145 _87967 _87968 f s P y) = (term138 _87967 _87968 f s P y).
Proof. exact (eq_refl (term145 _87967 _87968 f s P y)). Qed.
Lemma lem3386215 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3386216 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term151 _87967 _87968 f s P y) = (term152 _87967 _87968 f s P y).
Proof. exact (MK_COMB (@lem3386215) (@lem3386214 _87967 _87968 f s P y)). Qed.
Lemma lem3386217 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term95 _87967 _87968 s P f) = (term95 _87967 _87968 s P f).
Proof. exact (eq_refl (term95 _87967 _87968 s P f)). Qed.
Lemma lem3386218 {_87967 _87968 : Type'} (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term153 _87967 _87968 y s P f) = (term154 _87967 _87968 y s P f).
Proof. exact (MK_COMB (@lem3386216 _87967 _87968 f s P y) (@lem3386217 _87967 _87968 s P f)). Qed.
Lemma lem3386219 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term155 _87967 _87968 s P f) = (term156 _87967 _87968 s P f).
Proof. exact (fun_ext (fun y : _87967 => @lem3386218 _87967 _87968 y s P f)). Qed.
Lemma lem3386220 {_87967 : Type'} : (@ex _87967) = (@ex _87967).
Proof. exact (eq_refl (@ex _87967)). Qed.
Lemma lem3386221 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term144 _87967 _87968 s P f) = (term157 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3386220 _87967) (@lem3386219 _87967 _87968 s P f)). Qed.
Lemma lem3386222 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : ((term143 _87967 _87968 s P f) = (term144 _87967 _87968 s P f)) = ((term142 _87967 _87968 s P f) = (term157 _87967 _87968 s P f)).
Proof. exact (MK_COMB (@lem3386213 _87967 _87968 s P f) (@lem3386221 _87967 _87968 s P f)). Qed.
Lemma lem3386223 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term142 _87967 _87968 s P f) = (term157 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem3386222 _87967 _87968 s P f) (@lem3386203 _87967 _87968 s P f)). Qed.
Lemma lem3386225 {A : Type'} (P : A -> Prop) (Q : Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3386226 {_87968 : Type'} (P : _87968 -> Prop) (Q : Prop) : (term123 _87968 P Q) = (term124 _87968 P Q).
Proof. exact (@lem3386225 _87968 P Q). Qed.
Lemma lem3386227 {_87967 _87968 : Type'} (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term158 _87967 _87968 y s P f) = (term159 _87967 _87968 y s P f).
Proof. exact (@lem3386226 _87968 (term137 _87967 _87968 f s P y) (term95 _87967 _87968 s P f)). Qed.
Lemma lem3386228 {_87967 _87968 : Type'} (f : _87968 -> _87967) (x : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term160 _87967 _87968 f s P y x) = (term135 _87967 _87968 f x s P y).
Proof. exact (eq_refl (term160 _87967 _87968 f s P y x)). Qed.
Lemma lem3386229 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term161 _87967 _87968 f s P y) = (term137 _87967 _87968 f s P y).
Proof. exact (fun_ext (fun x : _87968 => @lem3386228 _87967 _87968 f x s P y)). Qed.
Lemma lem3386230 {_87968 : Type'} : (@ex _87968) = (@ex _87968).
Proof. exact (eq_refl (@ex _87968)). Qed.
Lemma lem3386231 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term162 _87967 _87968 f s P y) = (term138 _87967 _87968 f s P y).
Proof. exact (MK_COMB (@lem3386230 _87968) (@lem3386229 _87967 _87968 f s P y)). Qed.
Lemma lem3386232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3386233 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term163 _87967 _87968 f s P y) = (term152 _87967 _87968 f s P y).
Proof. exact (MK_COMB (@lem3386232) (@lem3386231 _87967 _87968 f s P y)). Qed.
Lemma lem3386234 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term95 _87967 _87968 s P f) = (term95 _87967 _87968 s P f).
Proof. exact (eq_refl (term95 _87967 _87968 s P f)). Qed.
Lemma lem3386235 {_87967 _87968 : Type'} (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term158 _87967 _87968 y s P f) = (term154 _87967 _87968 y s P f).
Proof. exact (MK_COMB (@lem3386233 _87967 _87968 f s P y) (@lem3386234 _87967 _87968 s P f)). Qed.
Lemma lem3386236 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3386237 {_87967 _87968 : Type'} (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term164 _87967 _87968 y s P f) = (term165 _87967 _87968 y s P f).
Proof. exact (MK_COMB (@lem3386236) (@lem3386235 _87967 _87968 y s P f)). Qed.
Lemma lem3386238 {_87967 _87968 : Type'} (f : _87968 -> _87967) (x : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term160 _87967 _87968 f s P y x) = (term135 _87967 _87968 f x s P y).
Proof. exact (eq_refl (term160 _87967 _87968 f s P y x)). Qed.
Lemma lem3386239 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3386240 {_87967 _87968 : Type'} (f : _87968 -> _87967) (x : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term166 _87967 _87968 f s P y x) = (term167 _87967 _87968 f x s P y).
Proof. exact (MK_COMB (@lem3386239) (@lem3386238 _87967 _87968 f x s P y)). Qed.
Lemma lem3386241 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term95 _87967 _87968 s P f) = (term95 _87967 _87968 s P f).
Proof. exact (eq_refl (term95 _87967 _87968 s P f)). Qed.
Lemma lem3386242 {_87967 _87968 : Type'} (x : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term168 _87967 _87968 y x s P f) = (term169 _87967 _87968 x y s P f).
Proof. exact (MK_COMB (@lem3386240 _87967 _87968 f x s P y) (@lem3386241 _87967 _87968 s P f)). Qed.
Lemma lem3386243 {_87967 _87968 : Type'} (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term170 _87967 _87968 y s P f) = (term171 _87967 _87968 y s P f).
Proof. exact (fun_ext (fun x : _87968 => @lem3386242 _87967 _87968 x y s P f)). Qed.
Lemma lem3386244 {_87968 : Type'} : (@ex _87968) = (@ex _87968).
Proof. exact (eq_refl (@ex _87968)). Qed.
Lemma lem3386245 {_87967 _87968 : Type'} (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term159 _87967 _87968 y s P f) = (term172 _87967 _87968 y s P f).
Proof. exact (MK_COMB (@lem3386244 _87968) (@lem3386243 _87967 _87968 y s P f)). Qed.
Lemma lem3386246 {_87967 _87968 : Type'} (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : ((term158 _87967 _87968 y s P f) = (term159 _87967 _87968 y s P f)) = ((term154 _87967 _87968 y s P f) = (term172 _87967 _87968 y s P f)).
Proof. exact (MK_COMB (@lem3386237 _87967 _87968 y s P f) (@lem3386245 _87967 _87968 y s P f)). Qed.
Lemma lem3386247 {_87967 _87968 : Type'} (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term154 _87967 _87968 y s P f) = (term172 _87967 _87968 y s P f).
Proof. exact (EQ_MP (@lem3386246 _87967 _87968 y s P f) (@lem3386227 _87967 _87968 y s P f)). Qed.
Lemma lem3386248 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term156 _87967 _87968 s P f) = (term173 _87967 _87968 s P f).
Proof. exact (fun_ext (fun y : _87967 => @lem3386247 _87967 _87968 y s P f)). Qed.
Lemma lem3386249 {_87967 : Type'} : (@ex _87967) = (@ex _87967).
Proof. exact (eq_refl (@ex _87967)). Qed.
Lemma lem3386250 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term157 _87967 _87968 s P f) = (term174 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3386249 _87967) (@lem3386248 _87967 _87968 s P f)). Qed.
Lemma lem3386251 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term142 _87967 _87968 s P f) = (term174 _87967 _87968 s P f).
Proof. exact (TRANS (@lem3386223 _87967 _87968 s P f) (@lem3386250 _87967 _87968 s P f)). Qed.
Lemma lem3386252 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term99 _87967 _87968 s P f) = (term174 _87967 _87968 s P f).
Proof. exact (TRANS (@lem3386199 _87967 _87968 s P f) (@lem3386251 _87967 _87968 s P f)). Qed.
Lemma lem3386253 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term107 _87967 _87968 s P f) = (term175 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3386168 _87967 _87968 s P f) (@lem3386252 _87967 _87968 s P f)). Qed.
Lemma lem3386257 {A : Type'} (P : A -> Prop) (Q : Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3386258 {_87968 : Type'} (P : _87968 -> Prop) (Q : Prop) : (term176 _87968 P Q) = (term177 _87968 P Q).
Proof. exact (@lem3386257 _87968 P Q). Qed.
Lemma lem3386259 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term178 _87967 _87968 s P f) = (term179 _87967 _87968 s P f).
Proof. exact (@lem3386258 _87968 (term120 _87967 _87968 s P f) (term174 _87967 _87968 s P f)). Qed.
Lemma lem3386260 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term180 _87967 _87968 s P f x) = (term118 _87967 _87968 s P f x).
Proof. exact (eq_refl (term180 _87967 _87968 s P f x)). Qed.
Lemma lem3386261 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term181 _87967 _87968 s P f) = (term120 _87967 _87968 s P f).
Proof. exact (fun_ext (fun x : _87968 => @lem3386260 _87967 _87968 s P f x)). Qed.
Lemma lem3386262 {_87968 : Type'} : (@ex _87968) = (@ex _87968).
Proof. exact (eq_refl (@ex _87968)). Qed.
Lemma lem3386263 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term182 _87967 _87968 s P f) = (term121 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3386262 _87968) (@lem3386261 _87967 _87968 s P f)). Qed.
Lemma lem3386264 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3386265 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term183 _87967 _87968 s P f) = (term122 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3386264) (@lem3386263 _87967 _87968 s P f)). Qed.
Lemma lem3386266 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term174 _87967 _87968 s P f) = (term174 _87967 _87968 s P f).
Proof. exact (eq_refl (term174 _87967 _87968 s P f)). Qed.
Lemma lem3386267 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term178 _87967 _87968 s P f) = (term175 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3386265 _87967 _87968 s P f) (@lem3386266 _87967 _87968 s P f)). Qed.
Lemma lem3386268 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3386269 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term184 _87967 _87968 s P f) = (term185 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3386268) (@lem3386267 _87967 _87968 s P f)). Qed.
Lemma lem3386270 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term180 _87967 _87968 s P f x) = (term118 _87967 _87968 s P f x).
Proof. exact (eq_refl (term180 _87967 _87968 s P f x)). Qed.
Lemma lem3386271 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3386272 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term186 _87967 _87968 s P f x) = (term187 _87967 _87968 s P f x).
Proof. exact (MK_COMB (@lem3386271) (@lem3386270 _87967 _87968 s P f x)). Qed.
Lemma lem3386273 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term174 _87967 _87968 s P f) = (term174 _87967 _87968 s P f).
Proof. exact (eq_refl (term174 _87967 _87968 s P f)). Qed.
Lemma lem3386274 {_87967 _87968 : Type'} (x : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term188 _87967 _87968 x s P f) = (term189 _87967 _87968 x s P f).
Proof. exact (MK_COMB (@lem3386272 _87967 _87968 s P f x) (@lem3386273 _87967 _87968 s P f)). Qed.
Lemma lem3386275 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term190 _87967 _87968 s P f) = (term191 _87967 _87968 s P f).
Proof. exact (fun_ext (fun x : _87968 => @lem3386274 _87967 _87968 x s P f)). Qed.
Lemma lem3386276 {_87968 : Type'} : (@ex _87968) = (@ex _87968).
Proof. exact (eq_refl (@ex _87968)). Qed.
Lemma lem3386277 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term179 _87967 _87968 s P f) = (term192 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3386276 _87968) (@lem3386275 _87967 _87968 s P f)). Qed.
Lemma lem3386278 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : ((term178 _87967 _87968 s P f) = (term179 _87967 _87968 s P f)) = ((term175 _87967 _87968 s P f) = (term192 _87967 _87968 s P f)).
Proof. exact (MK_COMB (@lem3386269 _87967 _87968 s P f) (@lem3386277 _87967 _87968 s P f)). Qed.
Lemma lem3386279 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term175 _87967 _87968 s P f) = (term192 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem3386278 _87967 _87968 s P f) (@lem3386259 _87967 _87968 s P f)). Qed.
Lemma lem3386281 {A : Type'} (P : Prop) (Q : A -> Prop) : (term193 A P Q) = (term194 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3386282 {_87967 : Type'} (P : Prop) (Q : _87967 -> Prop) : (term193 _87967 P Q) = (term194 _87967 P Q).
Proof. exact (@lem3386281 _87967 P Q). Qed.
Lemma lem3386283 {_87967 _87968 : Type'} (x : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term195 _87967 _87968 x s P f) = (term196 _87967 _87968 x s P f).
Proof. exact (@lem3386282 _87967 (term118 _87967 _87968 s P f x) (term173 _87967 _87968 s P f)). Qed.
Lemma lem3386284 {_87967 _87968 : Type'} (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term197 _87967 _87968 s P f y) = (term172 _87967 _87968 y s P f).
Proof. exact (eq_refl (term197 _87967 _87968 s P f y)). Qed.
Lemma lem3386285 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term198 _87967 _87968 s P f) = (term173 _87967 _87968 s P f).
Proof. exact (fun_ext (fun y : _87967 => @lem3386284 _87967 _87968 y s P f)). Qed.
Lemma lem3386286 {_87967 : Type'} : (@ex _87967) = (@ex _87967).
Proof. exact (eq_refl (@ex _87967)). Qed.
Lemma lem3386287 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term199 _87967 _87968 s P f) = (term174 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3386286 _87967) (@lem3386285 _87967 _87968 s P f)). Qed.
Lemma lem3386288 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term187 _87967 _87968 s P f x) = (term187 _87967 _87968 s P f x).
Proof. exact (eq_refl (term187 _87967 _87968 s P f x)). Qed.
Lemma lem3386289 {_87967 _87968 : Type'} (x : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term195 _87967 _87968 x s P f) = (term189 _87967 _87968 x s P f).
Proof. exact (MK_COMB (@lem3386288 _87967 _87968 s P f x) (@lem3386287 _87967 _87968 s P f)). Qed.
Lemma lem3386290 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3386291 {_87967 _87968 : Type'} (x : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term200 _87967 _87968 x s P f) = (term201 _87967 _87968 x s P f).
Proof. exact (MK_COMB (@lem3386290) (@lem3386289 _87967 _87968 x s P f)). Qed.
Lemma lem3386292 {_87967 _87968 : Type'} (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term197 _87967 _87968 s P f y) = (term172 _87967 _87968 y s P f).
Proof. exact (eq_refl (term197 _87967 _87968 s P f y)). Qed.
Lemma lem3386293 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term187 _87967 _87968 s P f x) = (term187 _87967 _87968 s P f x).
Proof. exact (eq_refl (term187 _87967 _87968 s P f x)). Qed.
Lemma lem3386294 {_87967 _87968 : Type'} (x : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term202 _87967 _87968 x s P f y) = (term203 _87967 _87968 x y s P f).
Proof. exact (MK_COMB (@lem3386293 _87967 _87968 s P f x) (@lem3386292 _87967 _87968 y s P f)). Qed.
Lemma lem3386295 {_87967 _87968 : Type'} (x : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term204 _87967 _87968 x s P f) = (term205 _87967 _87968 x s P f).
Proof. exact (fun_ext (fun y : _87967 => @lem3386294 _87967 _87968 x y s P f)). Qed.
Lemma lem3386296 {_87967 : Type'} : (@ex _87967) = (@ex _87967).
Proof. exact (eq_refl (@ex _87967)). Qed.
Lemma lem3386297 {_87967 _87968 : Type'} (x : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term196 _87967 _87968 x s P f) = (term206 _87967 _87968 x s P f).
Proof. exact (MK_COMB (@lem3386296 _87967) (@lem3386295 _87967 _87968 x s P f)). Qed.
Lemma lem3386298 {_87967 _87968 : Type'} (x : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : ((term195 _87967 _87968 x s P f) = (term196 _87967 _87968 x s P f)) = ((term189 _87967 _87968 x s P f) = (term206 _87967 _87968 x s P f)).
Proof. exact (MK_COMB (@lem3386291 _87967 _87968 x s P f) (@lem3386297 _87967 _87968 x s P f)). Qed.
Lemma lem3386299 {_87967 _87968 : Type'} (x : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term189 _87967 _87968 x s P f) = (term206 _87967 _87968 x s P f).
Proof. exact (EQ_MP (@lem3386298 _87967 _87968 x s P f) (@lem3386283 _87967 _87968 x s P f)). Qed.
Lemma lem3386301 {A : Type'} (P : Prop) (Q : A -> Prop) : (term193 A P Q) = (term194 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3386302 {_87968 : Type'} (P : Prop) (Q : _87968 -> Prop) : (term193 _87968 P Q) = (term194 _87968 P Q).
Proof. exact (@lem3386301 _87968 P Q). Qed.
Lemma lem3386303 {_87967 _87968 : Type'} (x : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term207 _87967 _87968 x y s P f) = (term208 _87967 _87968 x y s P f).
Proof. exact (@lem3386302 _87968 (term118 _87967 _87968 s P f x) (term171 _87967 _87968 y s P f)). Qed.
Lemma lem3386304 {_87967 _87968 : Type'} (x : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term209 _87967 _87968 y s P f x) = (term169 _87967 _87968 x y s P f).
Proof. exact (eq_refl (term209 _87967 _87968 y s P f x)). Qed.
Lemma lem3386305 {_87967 _87968 : Type'} (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term210 _87967 _87968 y s P f) = (term171 _87967 _87968 y s P f).
Proof. exact (fun_ext (fun x : _87968 => @lem3386304 _87967 _87968 x y s P f)). Qed.
Lemma lem3386306 {_87968 : Type'} : (@ex _87968) = (@ex _87968).
Proof. exact (eq_refl (@ex _87968)). Qed.
Lemma lem3386307 {_87967 _87968 : Type'} (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term211 _87967 _87968 y s P f) = (term172 _87967 _87968 y s P f).
Proof. exact (MK_COMB (@lem3386306 _87968) (@lem3386305 _87967 _87968 y s P f)). Qed.
Lemma lem3386308 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term187 _87967 _87968 s P f x) = (term187 _87967 _87968 s P f x).
Proof. exact (eq_refl (term187 _87967 _87968 s P f x)). Qed.
Lemma lem3386309 {_87967 _87968 : Type'} (x : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term207 _87967 _87968 x y s P f) = (term203 _87967 _87968 x y s P f).
Proof. exact (MK_COMB (@lem3386308 _87967 _87968 s P f x) (@lem3386307 _87967 _87968 y s P f)). Qed.
Lemma lem3386310 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3386311 {_87967 _87968 : Type'} (x : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term212 _87967 _87968 x y s P f) = (term213 _87967 _87968 x y s P f).
Proof. exact (MK_COMB (@lem3386310) (@lem3386309 _87967 _87968 x y s P f)). Qed.
Lemma lem3386312 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term209 _87967 _87968 y s P f x') = (term169 _87967 _87968 x' y s P f).
Proof. exact (eq_refl (term209 _87967 _87968 y s P f x')). Qed.
Lemma lem3386313 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term187 _87967 _87968 s P f x) = (term187 _87967 _87968 s P f x).
Proof. exact (eq_refl (term187 _87967 _87968 s P f x)). Qed.
Lemma lem3386314 {_87967 _87968 : Type'} (x : _87968) (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term214 _87967 _87968 x y s P f x') = (term215 _87967 _87968 x x' y s P f).
Proof. exact (MK_COMB (@lem3386313 _87967 _87968 s P f x) (@lem3386312 _87967 _87968 x' y s P f)). Qed.
Lemma lem3386315 {_87967 _87968 : Type'} (x : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term216 _87967 _87968 x y s P f) = (term217 _87967 _87968 x y s P f).
Proof. exact (fun_ext (fun x' : _87968 => @lem3386314 _87967 _87968 x x' y s P f)). Qed.
Lemma lem3386316 {_87968 : Type'} : (@ex _87968) = (@ex _87968).
Proof. exact (eq_refl (@ex _87968)). Qed.
Lemma lem3386317 {_87967 _87968 : Type'} (x : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term208 _87967 _87968 x y s P f) = (term218 _87967 _87968 x y s P f).
Proof. exact (MK_COMB (@lem3386316 _87968) (@lem3386315 _87967 _87968 x y s P f)). Qed.
Lemma lem3386318 {_87967 _87968 : Type'} (x : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : ((term207 _87967 _87968 x y s P f) = (term208 _87967 _87968 x y s P f)) = ((term203 _87967 _87968 x y s P f) = (term218 _87967 _87968 x y s P f)).
Proof. exact (MK_COMB (@lem3386311 _87967 _87968 x y s P f) (@lem3386317 _87967 _87968 x y s P f)). Qed.
Lemma lem3386319 {_87967 _87968 : Type'} (x : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term203 _87967 _87968 x y s P f) = (term218 _87967 _87968 x y s P f).
Proof. exact (EQ_MP (@lem3386318 _87967 _87968 x y s P f) (@lem3386303 _87967 _87968 x y s P f)). Qed.
Lemma lem3386320 {_87967 _87968 : Type'} (x : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term205 _87967 _87968 x s P f) = (term219 _87967 _87968 x s P f).
Proof. exact (fun_ext (fun y : _87967 => @lem3386319 _87967 _87968 x y s P f)). Qed.
Lemma lem3386321 {_87967 : Type'} : (@ex _87967) = (@ex _87967).
Proof. exact (eq_refl (@ex _87967)). Qed.
Lemma lem3386322 {_87967 _87968 : Type'} (x : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term206 _87967 _87968 x s P f) = (term220 _87967 _87968 x s P f).
Proof. exact (MK_COMB (@lem3386321 _87967) (@lem3386320 _87967 _87968 x s P f)). Qed.
Lemma lem3386323 {_87967 _87968 : Type'} (x : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term189 _87967 _87968 x s P f) = (term220 _87967 _87968 x s P f).
Proof. exact (TRANS (@lem3386299 _87967 _87968 x s P f) (@lem3386322 _87967 _87968 x s P f)). Qed.
Lemma lem3386324 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term191 _87967 _87968 s P f) = (term221 _87967 _87968 s P f).
Proof. exact (fun_ext (fun x : _87968 => @lem3386323 _87967 _87968 x s P f)). Qed.
Lemma lem3386325 {_87968 : Type'} : (@ex _87968) = (@ex _87968).
Proof. exact (eq_refl (@ex _87968)). Qed.
Lemma lem3386326 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term192 _87967 _87968 s P f) = (term222 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3386325 _87968) (@lem3386324 _87967 _87968 s P f)). Qed.
Lemma lem3386327 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term175 _87967 _87968 s P f) = (term222 _87967 _87968 s P f).
Proof. exact (TRANS (@lem3386279 _87967 _87968 s P f) (@lem3386326 _87967 _87968 s P f)). Qed.
Lemma lem3386329 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term107 _87967 _87968 s P f) = (term222 _87967 _87968 s P f).
Proof. exact (TRANS (@lem3386253 _87967 _87968 s P f) (@lem3386327 _87967 _87968 s P f)). Qed.
Lemma lem3386330 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term52 _87967 _87968 s P f) = (term222 _87967 _87968 s P f).
Proof. exact (TRANS (@lem3385873 _87967 _87968 s P f) (@lem3386329 _87967 _87968 s P f)). Qed.
Lemma lem3386331 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term52 _87967 _87968 s P f) : term222 _87967 _87968 s P f.
Proof. exact (EQ_MP (@lem3386330 _87967 _87968 s P f) (@lem3385785 _87967 _87968 s P f h1)). Qed.
Lemma lem3386332 {_87967 _87968 : Type'} (x : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term220 _87967 _87968 x s P f) : term220 _87967 _87968 x s P f.
Proof. exact (h1). Qed.
Lemma lem3386333 {_87967 _87968 : Type'} (x : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term218 _87967 _87968 x y s P f) : term218 _87967 _87968 x y s P f.
Proof. exact (h1). Qed.
Lemma lem3386334 {_87967 _87968 : Type'} (x : _87968) (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term215 _87967 _87968 x x' y s P f) : term215 _87967 _87968 x x' y s P f.
Proof. exact (h1). Qed.
Lemma lem3386349 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term86 _87967 _87968 s P f x) = (term86 _87967 _87968 s P f x).
Proof. exact (eq_refl (term86 _87967 _87968 s P f x)). Qed.
Lemma lem3386350 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term94 _87967 _87968 s P f) = (term94 _87967 _87968 s P f).
Proof. exact (fun_ext (fun x : _87968 => @lem3386349 _87967 _87968 s P f x)). Qed.
Lemma lem3386351 {_87968 : Type'} : (@all _87968) = (@all _87968).
Proof. exact (eq_refl (@all _87968)). Qed.
Lemma lem3386352 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term95 _87967 _87968 s P f) = (term95 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3386351 _87968) (@lem3386350 _87967 _87968 s P f)). Qed.
Lemma lem3386377 {_87967 _87968 : Type'} (f : _87968 -> _87967) (x' : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term167 _87967 _87968 f x' s P y) = (term167 _87967 _87968 f x' s P y).
Proof. exact (eq_refl (term167 _87967 _87968 f x' s P y)). Qed.
Lemma lem3386378 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term169 _87967 _87968 x' y s P f) = (term169 _87967 _87968 x' y s P f).
Proof. exact (MK_COMB (@lem3386377 _87967 _87968 f x' s P y) (@lem3386352 _87967 _87968 s P f)). Qed.
Lemma lem3386393 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term84 _87967 _87968 s P f x) = (term84 _87967 _87968 s P f x).
Proof. exact (eq_refl (term84 _87967 _87968 s P f x)). Qed.
Lemma lem3386396 {_87967 : Type'} (P : _87967 -> Prop) (y : _87967) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem3386415 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (x : _87968) (s : _87968 -> Prop) : (term54 _87967 _87968 y f x s) = (term54 _87967 _87968 y f x s).
Proof. exact (eq_refl (term54 _87967 _87968 y f x s)). Qed.
Lemma lem3386416 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term62 _87967 _87968 y f s) = (term62 _87967 _87968 y f s).
Proof. exact (fun_ext (fun x : _87968 => @lem3386415 _87967 _87968 y f x s)). Qed.
Lemma lem3386417 {_87968 : Type'} : (@all _87968) = (@all _87968).
Proof. exact (eq_refl (@all _87968)). Qed.
Lemma lem3386418 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term63 _87967 _87968 y f s) = (term63 _87967 _87968 y f s).
Proof. exact (MK_COMB (@lem3386417 _87968) (@lem3386416 _87967 _87968 y f s)). Qed.
Lemma lem3386419 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3386420 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term69 _87967 _87968 y f s) = (term69 _87967 _87968 y f s).
Proof. exact (MK_COMB (@lem3386419) (@lem3386418 _87967 _87968 y f s)). Qed.
Lemma lem3386421 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term71 _87967 _87968 f s P y) = (term71 _87967 _87968 f s P y).
Proof. exact (MK_COMB (@lem3386420 _87967 _87968 y f s) (@lem3386396 _87967 P y)). Qed.
Lemma lem3386422 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term81 _87967 _87968 f s P) = (term81 _87967 _87968 f s P).
Proof. exact (fun_ext (fun y : _87967 => @lem3386421 _87967 _87968 f s P y)). Qed.
Lemma lem3386423 {_87967 : Type'} : (@all _87967) = (@all _87967).
Proof. exact (eq_refl (@all _87967)). Qed.
Lemma lem3386424 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term82 _87967 _87968 f s P) = (term82 _87967 _87968 f s P).
Proof. exact (MK_COMB (@lem3386423 _87967) (@lem3386422 _87967 _87968 f s P)). Qed.
Lemma lem3386425 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3386426 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term101 _87967 _87968 f s P) = (term101 _87967 _87968 f s P).
Proof. exact (MK_COMB (@lem3386425) (@lem3386424 _87967 _87968 f s P)). Qed.
Lemma lem3386427 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term118 _87967 _87968 s P f x) = (term118 _87967 _87968 s P f x).
Proof. exact (MK_COMB (@lem3386426 _87967 _87968 f s P) (@lem3386393 _87967 _87968 s P f x)). Qed.
Lemma lem3386428 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3386429 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term187 _87967 _87968 s P f x) = (term187 _87967 _87968 s P f x).
Proof. exact (MK_COMB (@lem3386428) (@lem3386427 _87967 _87968 s P f x)). Qed.
Lemma lem3386430 {_87967 _87968 : Type'} (x : _87968) (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term215 _87967 _87968 x x' y s P f) = (term215 _87967 _87968 x x' y s P f).
Proof. exact (MK_COMB (@lem3386429 _87967 _87968 s P f x) (@lem3386378 _87967 _87968 x' y s P f)). Qed.
Lemma lem3386431 {_87967 _87968 : Type'} (x : _87968) (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term215 _87967 _87968 x x' y s P f) : term215 _87967 _87968 x x' y s P f.
Proof. exact (EQ_MP (@lem3386430 _87967 _87968 x x' y s P f) (@lem3386334 _87967 _87968 x x' y s P f h1)). Qed.
Lemma lem3386432 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : term118 _87967 _87968 s P f x.
Proof. exact (h1). Qed.
Lemma lem3386433 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : term169 _87967 _87968 x' y s P f.
Proof. exact (h1). Qed.
Lemma lem3386434 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : term84 _87967 _87968 s P f x.
Proof. exact (proj2 (@lem3386432 _87967 _87968 s P f x h1)). Qed.
Lemma lem3386435 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : term82 _87967 _87968 f s P.
Proof. exact (proj1 (@lem3386432 _87967 _87968 s P f x h1)). Qed.
Lemma lem3386438 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : term95 _87967 _87968 s P f.
Proof. exact (proj2 (@lem3386433 _87967 _87968 x' y s P f h1)). Qed.
Lemma lem3386439 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : term135 _87967 _87968 f x' s P y.
Proof. exact (proj1 (@lem3386433 _87967 _87968 x' y s P f h1)). Qed.
Lemma lem3386441 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : term49 _87967 _87968 y f x' s.
Proof. exact (proj1 (@lem3386439 _87967 _87968 x' y s P f h1)). Qed.
Lemma lem3386445 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3386446 {_87968 : Type'} (P : _87968 -> Prop) (Q : Prop) : (term223 _87968 P Q) = (term224 _87968 P Q).
Proof. exact (@lem3386445 _87968 P Q). Qed.
Lemma lem3386447 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term225 _87967 _87968 f s P y) = (term226 _87967 _87968 f s P y).
Proof. exact (@lem3386446 _87968 (term62 _87967 _87968 y f s) (P y)). Qed.
Lemma lem3386448 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (x : _87968) (s : _87968 -> Prop) : (term227 _87967 _87968 y f s x) = (term54 _87967 _87968 y f x s).
Proof. exact (eq_refl (term227 _87967 _87968 y f s x)). Qed.
Lemma lem3386449 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term228 _87967 _87968 y f s) = (term62 _87967 _87968 y f s).
Proof. exact (fun_ext (fun x : _87968 => @lem3386448 _87967 _87968 y f x s)). Qed.
Lemma lem3386450 {_87968 : Type'} : (@all _87968) = (@all _87968).
Proof. exact (eq_refl (@all _87968)). Qed.
Lemma lem3386451 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term229 _87967 _87968 y f s) = (term63 _87967 _87968 y f s).
Proof. exact (MK_COMB (@lem3386450 _87968) (@lem3386449 _87967 _87968 y f s)). Qed.
Lemma lem3386452 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3386453 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (s : _87968 -> Prop) : (term230 _87967 _87968 y f s) = (term69 _87967 _87968 y f s).
Proof. exact (MK_COMB (@lem3386452) (@lem3386451 _87967 _87968 y f s)). Qed.
Lemma lem3386454 {_87967 : Type'} (P : _87967 -> Prop) (y : _87967) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem3386455 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term225 _87967 _87968 f s P y) = (term71 _87967 _87968 f s P y).
Proof. exact (MK_COMB (@lem3386453 _87967 _87968 y f s) (@lem3386454 _87967 P y)). Qed.
Lemma lem3386456 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3386457 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term231 _87967 _87968 f s P y) = (term232 _87967 _87968 f s P y).
Proof. exact (MK_COMB (@lem3386456) (@lem3386455 _87967 _87968 f s P y)). Qed.
Lemma lem3386458 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (x : _87968) (s : _87968 -> Prop) : (term227 _87967 _87968 y f s x) = (term54 _87967 _87968 y f x s).
Proof. exact (eq_refl (term227 _87967 _87968 y f s x)). Qed.
Lemma lem3386459 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3386460 {_87967 _87968 : Type'} (y : _87967) (f : _87968 -> _87967) (x : _87968) (s : _87968 -> Prop) : (term233 _87967 _87968 y f s x) = (term234 _87967 _87968 y f x s).
Proof. exact (MK_COMB (@lem3386459) (@lem3386458 _87967 _87968 y f x s)). Qed.
Lemma lem3386461 {_87967 : Type'} (P : _87967 -> Prop) (y : _87967) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem3386462 {_87967 _87968 : Type'} (f : _87968 -> _87967) (x : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term235 _87967 _87968 f s x P y) = (term236 _87967 _87968 f x s P y).
Proof. exact (MK_COMB (@lem3386460 _87967 _87968 y f x s) (@lem3386461 _87967 P y)). Qed.
Lemma lem3386463 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term237 _87967 _87968 f s P y) = (term238 _87967 _87968 f s P y).
Proof. exact (fun_ext (fun x : _87968 => @lem3386462 _87967 _87968 f x s P y)). Qed.
Lemma lem3386464 {_87968 : Type'} : (@all _87968) = (@all _87968).
Proof. exact (eq_refl (@all _87968)). Qed.
Lemma lem3386465 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term226 _87967 _87968 f s P y) = (term239 _87967 _87968 f s P y).
Proof. exact (MK_COMB (@lem3386464 _87968) (@lem3386463 _87967 _87968 f s P y)). Qed.
Lemma lem3386466 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : ((term225 _87967 _87968 f s P y) = (term226 _87967 _87968 f s P y)) = ((term71 _87967 _87968 f s P y) = (term239 _87967 _87968 f s P y)).
Proof. exact (MK_COMB (@lem3386457 _87967 _87968 f s P y) (@lem3386465 _87967 _87968 f s P y)). Qed.
Lemma lem3386467 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term71 _87967 _87968 f s P y) = (term239 _87967 _87968 f s P y).
Proof. exact (EQ_MP (@lem3386466 _87967 _87968 f s P y) (@lem3386447 _87967 _87968 f s P y)). Qed.
Lemma lem3386468 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term81 _87967 _87968 f s P) = (term240 _87967 _87968 f s P).
Proof. exact (fun_ext (fun y : _87967 => @lem3386467 _87967 _87968 f s P y)). Qed.
Lemma lem3386469 {_87967 : Type'} : (@all _87967) = (@all _87967).
Proof. exact (eq_refl (@all _87967)). Qed.
Lemma lem3386470 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term82 _87967 _87968 f s P) = (term241 _87967 _87968 f s P).
Proof. exact (MK_COMB (@lem3386469 _87967) (@lem3386468 _87967 _87968 f s P)). Qed.
Lemma lem3386483 {_87967 _87968 : Type'} (f : _87968 -> _87967) (x : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term236 _87967 _87968 f x s P y) = (term236 _87967 _87968 f x s P y).
Proof. exact (eq_refl (term236 _87967 _87968 f x s P y)). Qed.
Lemma lem3386484 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term238 _87967 _87968 f s P y) = (term238 _87967 _87968 f s P y).
Proof. exact (fun_ext (fun x : _87968 => @lem3386483 _87967 _87968 f x s P y)). Qed.
Lemma lem3386485 {_87968 : Type'} : (@all _87968) = (@all _87968).
Proof. exact (eq_refl (@all _87968)). Qed.
Lemma lem3386486 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (y : _87967) : (term239 _87967 _87968 f s P y) = (term239 _87967 _87968 f s P y).
Proof. exact (MK_COMB (@lem3386485 _87968) (@lem3386484 _87967 _87968 f s P y)). Qed.
Lemma lem3386487 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term240 _87967 _87968 f s P) = (term240 _87967 _87968 f s P).
Proof. exact (fun_ext (fun y : _87967 => @lem3386486 _87967 _87968 f s P y)). Qed.
Lemma lem3386488 {_87967 : Type'} : (@all _87967) = (@all _87967).
Proof. exact (eq_refl (@all _87967)). Qed.
Lemma lem3386489 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term241 _87967 _87968 f s P) = (term241 _87967 _87968 f s P).
Proof. exact (MK_COMB (@lem3386488 _87967) (@lem3386487 _87967 _87968 f s P)). Qed.
Lemma lem3386490 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) : (term82 _87967 _87968 f s P) = (term241 _87967 _87968 f s P).
Proof. exact (TRANS (@lem3386470 _87967 _87968 f s P) (@lem3386489 _87967 _87968 f s P)). Qed.
Lemma lem3386491 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : term241 _87967 _87968 f s P.
Proof. exact (EQ_MP (@lem3386490 _87967 _87968 f s P) (@lem3386435 _87967 _87968 s P f x h1)). Qed.
Lemma lem3386507 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term86 _87967 _87968 s P f x) = (term86 _87967 _87968 s P f x).
Proof. exact (eq_refl (term86 _87967 _87968 s P f x)). Qed.
Lemma lem3386508 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term94 _87967 _87968 s P f) = (term94 _87967 _87968 s P f).
Proof. exact (fun_ext (fun x : _87968 => @lem3386507 _87967 _87968 s P f x)). Qed.
Lemma lem3386509 {_87968 : Type'} : (@all _87968) = (@all _87968).
Proof. exact (eq_refl (@all _87968)). Qed.
Lemma lem3386511 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term95 _87967 _87968 s P f) = (term95 _87967 _87968 s P f).
Proof. exact (MK_COMB (@lem3386509 _87968) (@lem3386508 _87967 _87968 s P f)). Qed.
Lemma lem3386512 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : term95 _87967 _87968 s P f.
Proof. exact (EQ_MP (@lem3386511 _87967 _87968 s P f) (@lem3386438 _87967 _87968 x' y s P f h1)). Qed.
Lemma lem3386525 {_87967 _87968 : Type'} (_35564 : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : term242 _87967 _87968 f s P _35564.
Proof. exact (@lem3386491 _87967 _87968 s P f x h1 _35564). Qed.
Lemma lem3386526 {_87967 _87968 : Type'} (f : _87968 -> _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (_35564 : _87967) : (term242 _87967 _87968 f s P _35564) = (term239 _87967 _87968 f s P _35564).
Proof. exact (eq_refl (term242 _87967 _87968 f s P _35564)). Qed.
Lemma lem3386527 {_87967 _87968 : Type'} (_35564 : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : term239 _87967 _87968 f s P _35564.
Proof. exact (EQ_MP (@lem3386526 _87967 _87968 f s P _35564) (@lem3386525 _87967 _87968 _35564 s P f x h1)). Qed.
Lemma lem3386528 {_87967 _87968 : Type'} (_35564 : _87967) (_35565 : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : term243 _87967 _87968 f s P _35564 _35565.
Proof. exact (@lem3386527 _87967 _87968 _35564 s P f x h1 _35565). Qed.
Lemma lem3386529 {_87967 _87968 : Type'} (f : _87968 -> _87967) (_35565 : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (_35564 : _87967) : (term243 _87967 _87968 f s P _35564 _35565) = (term236 _87967 _87968 f _35565 s P _35564).
Proof. exact (eq_refl (term243 _87967 _87968 f s P _35564 _35565)). Qed.
Lemma lem3386530 {_87967 _87968 : Type'} (_35565 : _87968) (_35564 : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : term236 _87967 _87968 f _35565 s P _35564.
Proof. exact (EQ_MP (@lem3386529 _87967 _87968 f _35565 s P _35564) (@lem3386528 _87967 _87968 _35564 _35565 s P f x h1)). Qed.
Lemma lem3386531 {_87967 _87968 : Type'} (_35566 : _87968) (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : term244 _87967 _87968 s P f _35566.
Proof. exact (@lem3386512 _87967 _87968 x' y s P f h1 _35566). Qed.
Lemma lem3386532 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (_35566 : _87968) : (term244 _87967 _87968 s P f _35566) = (term86 _87967 _87968 s P f _35566).
Proof. exact (eq_refl (term244 _87967 _87968 s P f _35566)). Qed.
Lemma lem3386544 {_87967 _87968 : Type'} (f : _87968 -> _87967) (_35565 : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (_35564 : _87967) : (term236 _87967 _87968 f _35565 s P _35564) = (term245 _87967 _87968 f _35565 s P _35564).
Proof. exact (@lem3385510 (term246 _87967 _87968 _35564 f _35565) (term247 _87968 _35565 s) (P _35564)). Qed.
Lemma lem3386545 {_87967 _87968 : Type'} (_35565 : _87968) (_35564 : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : term245 _87967 _87968 f _35565 s P _35564.
Proof. exact (EQ_MP (@lem3386544 _87967 _87968 f _35565 s P _35564) (@lem3386530 _87967 _87968 _35565 _35564 s P f x h1)). Qed.
Lemma lem3386549 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : term248 _87967 _87968 P f x.
Proof. exact (proj2 (@lem3386434 _87967 _87968 s P f x h1)). Qed.
Lemma lem3386557 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : term64 _87967 P y.
Proof. exact (proj2 (@lem3386439 _87967 _87968 x' y s P f h1)). Qed.
Lemma lem3386559 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : y = (f x').
Proof. exact (proj1 (@lem3386441 _87967 _87968 x' y s P f h1)). Qed.
Lemma lem3386589 {_87967 _87968 : Type'} (_35566 : _87968) (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : term86 _87967 _87968 s P f _35566.
Proof. exact (EQ_MP (@lem3386532 _87967 _87968 s P f _35566) (@lem3386531 _87967 _87968 _35566 x' y s P f h1)). Qed.
Lemma lem3386590 {_87967 : Type'} (P : _87967 -> Prop) : (term249 _87967 P) = (term249 _87967 P).
Proof. exact (eq_refl (term249 _87967 P)). Qed.
Lemma lem3386591 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : (term250 _87967 P y) = (term251 _87967 _87968 P f x').
Proof. exact (MK_COMB (@lem3386590 _87967 P) (@lem3386559 _87967 _87968 x' y s P f h1)). Qed.
Lemma lem3386592 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (x' : _87968) : (term251 _87967 _87968 P f x') = (term248 _87967 _87968 P f x').
Proof. exact (eq_refl (term251 _87967 _87968 P f x')). Qed.
Lemma lem3386593 {_87967 : Type'} (P : _87967 -> Prop) (y : _87967) : (term252 _87967 P y) = (term252 _87967 P y).
Proof. exact (eq_refl (term252 _87967 P y)). Qed.
Lemma lem3386594 {_87967 _87968 : Type'} (y : _87967) (P : _87967 -> Prop) (f : _87968 -> _87967) (x' : _87968) : ((term250 _87967 P y) = (term251 _87967 _87968 P f x')) = ((term250 _87967 P y) = (term248 _87967 _87968 P f x')).
Proof. exact (MK_COMB (@lem3386593 _87967 P y) (@lem3386592 _87967 _87968 P f x')). Qed.
Lemma lem3386595 {_87967 : Type'} (P : _87967 -> Prop) (y : _87967) : (term250 _87967 P y) = (term64 _87967 P y).
Proof. exact (eq_refl (term250 _87967 P y)). Qed.
Lemma lem3386596 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3386597 {_87967 : Type'} (P : _87967 -> Prop) (y : _87967) : (term252 _87967 P y) = (term253 _87967 P y).
Proof. exact (MK_COMB (@lem3386596) (@lem3386595 _87967 P y)). Qed.
Lemma lem3386598 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (x' : _87968) : (term248 _87967 _87968 P f x') = (term248 _87967 _87968 P f x').
Proof. exact (eq_refl (term248 _87967 _87968 P f x')). Qed.
Lemma lem3386599 {_87967 _87968 : Type'} (y : _87967) (P : _87967 -> Prop) (f : _87968 -> _87967) (x' : _87968) : ((term250 _87967 P y) = (term248 _87967 _87968 P f x')) = ((term64 _87967 P y) = (term248 _87967 _87968 P f x')).
Proof. exact (MK_COMB (@lem3386597 _87967 P y) (@lem3386598 _87967 _87968 P f x')). Qed.
Lemma lem3386600 {_87967 _87968 : Type'} (y : _87967) (P : _87967 -> Prop) (f : _87968 -> _87967) (x' : _87968) : ((term250 _87967 P y) = (term251 _87967 _87968 P f x')) = ((term64 _87967 P y) = (term248 _87967 _87968 P f x')).
Proof. exact (TRANS (@lem3386594 _87967 _87968 y P f x') (@lem3386599 _87967 _87968 y P f x')). Qed.
Lemma lem3386601 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : (term64 _87967 P y) = (term248 _87967 _87968 P f x').
Proof. exact (EQ_MP (@lem3386600 _87967 _87968 y P f x') (@lem3386591 _87967 _87968 x' y s P f h1)). Qed.
Lemma lem3386602 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : term248 _87967 _87968 P f x'.
Proof. exact (EQ_MP (@lem3386601 _87967 _87968 x' y s P f h1) (@lem3386557 _87967 _87968 x' y s P f h1)). Qed.
Lemma lem3386663 {_87967 : Type'} (x : _87967) : x = x.
Proof. exact (@lem21386 _87967 x). Qed.
Lemma lem3386664 {_87967 : Type'} (x : _87967) : x = x.
Proof. exact (@lem3386663 _87967 x). Qed.
Lemma lem3386665 {_87967 _87968 : Type'} (f : _87968 -> _87967) (x : _87968) : (f x) = (f x).
Proof. exact (@lem3386664 _87967 (f x)). Qed.
Lemma lem3386666 {_87967 _87968 : Type'} (f : _87968 -> _87967) (x : _87968) : term254 _87967 _87968 f x.
Proof. exact (fun h0 : term255 _87967 _87968 f x => @lem3386665 _87967 _87968 f x). Qed.
Lemma lem3386668 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3386669 {_87967 _87968 : Type'} (f : _87968 -> _87967) (x : _87968) : (term254 _87967 _87968 f x) = ((f x) = (f x)).
Proof. exact (@lem3386668 ((f x) = (f x))). Qed.
Lemma lem3386670 {_87967 _87968 : Type'} (f : _87968 -> _87967) (x : _87968) : (f x) = (f x).
Proof. exact (EQ_MP (@lem3386669 _87967 _87968 f x) (@lem3386666 _87967 _87968 f x)). Qed.
Lemma lem3386672 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : @IN _87968 x s.
Proof. exact (proj1 (@lem3386434 _87967 _87968 s P f x h1)). Qed.
Lemma lem3386673 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : term257 _87968 x s.
Proof. exact (fun h0 : term247 _87968 x s => @lem3386672 _87967 _87968 s P f x h1). Qed.
Lemma lem3386675 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3386676 {_87968 : Type'} (x : _87968) (s : _87968 -> Prop) : (term257 _87968 x s) = (@IN _87968 x s).
Proof. exact (@lem3386675 (@IN _87968 x s)). Qed.
Lemma lem3386677 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : @IN _87968 x s.
Proof. exact (EQ_MP (@lem3386676 _87968 x s) (@lem3386673 _87967 _87968 s P f x h1)). Qed.
Lemma lem3386695 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3386696 {_87967 _87968 : Type'} (P : _87967 -> Prop) (_35564 : _87967) (_35565 : _87968) (s : _87968 -> Prop) : (term258 _87967 _87968 _35565 s P _35564) = (term259 _87967 _87968 P _35564 _35565 s).
Proof. exact (@lem3386695 (P _35564) (term247 _87968 _35565 s)). Qed.
Lemma lem3386702 {_87967 _87968 : Type'} (_35564 : _87967) (f : _87968 -> _87967) (_35565 : _87968) : (term260 _87967 _87968 _35564 f _35565) = (term260 _87967 _87968 _35564 f _35565).
Proof. exact (eq_refl (term260 _87967 _87968 _35564 f _35565)). Qed.
Lemma lem3386703 {_87967 _87968 : Type'} (f : _87968 -> _87967) (P : _87967 -> Prop) (_35564 : _87967) (_35565 : _87968) (s : _87968 -> Prop) : (term245 _87967 _87968 f _35565 s P _35564) = (term261 _87967 _87968 f P _35564 _35565 s).
Proof. exact (MK_COMB (@lem3386702 _87967 _87968 _35564 f _35565) (@lem3386696 _87967 _87968 P _35564 _35565 s)). Qed.
Lemma lem3386707 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3386708 {_87967 _87968 : Type'} (P : _87967 -> Prop) (_35564 : _87967) (f : _87968 -> _87967) (_35565 : _87968) (s : _87968 -> Prop) : (term261 _87967 _87968 f P _35564 _35565 s) = (term262 _87967 _87968 P _35564 f _35565 s).
Proof. exact (@lem3386707 (P _35564) (term246 _87967 _87968 _35564 f _35565) (term247 _87968 _35565 s)). Qed.
Lemma lem3386726 {_87967 _87968 : Type'} (P : _87967 -> Prop) (_35564 : _87967) (f : _87968 -> _87967) (_35565 : _87968) (s : _87968 -> Prop) : (term245 _87967 _87968 f _35565 s P _35564) = (term262 _87967 _87968 P _35564 f _35565 s).
Proof. exact (TRANS (@lem3386703 _87967 _87968 f P _35564 _35565 s) (@lem3386708 _87967 _87968 P _35564 f _35565 s)). Qed.
Lemma lem3386727 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3386728 {_87967 _87968 : Type'} (P : _87967 -> Prop) (_35564 : _87967) (f : _87968 -> _87967) (_35565 : _87968) (s : _87968 -> Prop) : (term263 _87967 _87968 f _35565 s P _35564) = (term264 _87967 _87968 P _35564 f _35565 s).
Proof. exact (MK_COMB (@lem3386727) (@lem3386726 _87967 _87968 P _35564 f _35565 s)). Qed.
Lemma lem3386746 {_87967 _87968 : Type'} (P : _87967 -> Prop) (_35564 : _87967) (f : _87968 -> _87967) (_35565 : _87968) (s : _87968 -> Prop) : (term262 _87967 _87968 P _35564 f _35565 s) = (term262 _87967 _87968 P _35564 f _35565 s).
Proof. exact (eq_refl (term262 _87967 _87968 P _35564 f _35565 s)). Qed.
Lemma lem3386747 {_87967 _87968 : Type'} (P : _87967 -> Prop) (_35564 : _87967) (f : _87968 -> _87967) (_35565 : _87968) (s : _87968 -> Prop) : ((term245 _87967 _87968 f _35565 s P _35564) = (term262 _87967 _87968 P _35564 f _35565 s)) = ((term262 _87967 _87968 P _35564 f _35565 s) = (term262 _87967 _87968 P _35564 f _35565 s)).
Proof. exact (MK_COMB (@lem3386728 _87967 _87968 P _35564 f _35565 s) (@lem3386746 _87967 _87968 P _35564 f _35565 s)). Qed.
Lemma lem3386749 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3386750 (x : Prop) : (x = x) = True.
Proof. exact (@lem3386749 Prop x). Qed.
Lemma lem3386751 {_87967 _87968 : Type'} (P : _87967 -> Prop) (_35564 : _87967) (f : _87968 -> _87967) (_35565 : _87968) (s : _87968 -> Prop) : ((term262 _87967 _87968 P _35564 f _35565 s) = (term262 _87967 _87968 P _35564 f _35565 s)) = True.
Proof. exact (@lem3386750 (term262 _87967 _87968 P _35564 f _35565 s)). Qed.
Lemma lem3386752 {_87967 _87968 : Type'} (P : _87967 -> Prop) (_35564 : _87967) (f : _87968 -> _87967) (_35565 : _87968) (s : _87968 -> Prop) : ((term245 _87967 _87968 f _35565 s P _35564) = (term262 _87967 _87968 P _35564 f _35565 s)) = True.
Proof. exact (TRANS (@lem3386747 _87967 _87968 P _35564 f _35565 s) (@lem3386751 _87967 _87968 P _35564 f _35565 s)). Qed.
Lemma lem3386753 {_87967 _87968 : Type'} (P : _87967 -> Prop) (_35564 : _87967) (f : _87968 -> _87967) (_35565 : _87968) (s : _87968 -> Prop) : True = ((term245 _87967 _87968 f _35565 s P _35564) = (term262 _87967 _87968 P _35564 f _35565 s)).
Proof. exact (SYM (@lem3386752 _87967 _87968 P _35564 f _35565 s)). Qed.
Lemma lem3386754 {_87967 _87968 : Type'} (P : _87967 -> Prop) (_35564 : _87967) (f : _87968 -> _87967) (_35565 : _87968) (s : _87968 -> Prop) : (term245 _87967 _87968 f _35565 s P _35564) = (term262 _87967 _87968 P _35564 f _35565 s).
Proof. exact (EQ_MP (@lem3386753 _87967 _87968 P _35564 f _35565 s) (@lem0)). Qed.
Lemma lem3386755 {_87967 _87968 : Type'} (_35564 : _87967) (_35565 : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : term262 _87967 _87968 P _35564 f _35565 s.
Proof. exact (EQ_MP (@lem3386754 _87967 _87968 P _35564 f _35565 s) (@lem3386545 _87967 _87968 _35565 _35564 s P f x h1)). Qed.
Lemma lem3386757 (b : Prop) (a : Prop) : (a \/ b) = (term265 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3386758 {_87967 _87968 : Type'} (f : _87968 -> _87967) (_35565 : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (_35564 : _87967) : (term262 _87967 _87968 P _35564 f _35565 s) = (term266 _87967 _87968 f _35565 s P _35564).
Proof. exact (@lem3386757 (term54 _87967 _87968 _35564 f _35565 s) (P _35564)). Qed.
Lemma lem3386760 (a : Prop) (b : Prop) : (term267 a b) = (term268 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3386761 {_87967 _87968 : Type'} (_35564 : _87967) (f : _87968 -> _87967) (_35565 : _87968) (s : _87968 -> Prop) : (term269 _87967 _87968 _35564 f _35565 s) = (term270 _87967 _87968 _35564 f _35565 s).
Proof. exact (@lem3386760 (term246 _87967 _87968 _35564 f _35565) (term247 _87968 _35565 s)). Qed.
Lemma lem3386763 (a : Prop) : (term42 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3386764 {_87967 _87968 : Type'} (_35564 : _87967) (f : _87968 -> _87967) (_35565 : _87968) : (term271 _87967 _87968 _35564 f _35565) = (_35564 = (f _35565)).
Proof. exact (@lem3386763 (_35564 = (f _35565))). Qed.
Lemma lem3386765 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3386766 {_87967 _87968 : Type'} (_35564 : _87967) (f : _87968 -> _87967) (_35565 : _87968) : (term272 _87967 _87968 _35564 f _35565) = (term273 _87967 _87968 _35564 f _35565).
Proof. exact (MK_COMB (@lem3386765) (@lem3386764 _87967 _87968 _35564 f _35565)). Qed.
Lemma lem3386768 (a : Prop) : (term42 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3386769 {_87968 : Type'} (_35565 : _87968) (s : _87968 -> Prop) : (term274 _87968 _35565 s) = (@IN _87968 _35565 s).
Proof. exact (@lem3386768 (@IN _87968 _35565 s)). Qed.
Lemma lem3386770 {_87967 _87968 : Type'} (_35564 : _87967) (f : _87968 -> _87967) (_35565 : _87968) (s : _87968 -> Prop) : (term270 _87967 _87968 _35564 f _35565 s) = (term49 _87967 _87968 _35564 f _35565 s).
Proof. exact (MK_COMB (@lem3386766 _87967 _87968 _35564 f _35565) (@lem3386769 _87968 _35565 s)). Qed.
Lemma lem3386771 {_87967 _87968 : Type'} (_35564 : _87967) (f : _87968 -> _87967) (_35565 : _87968) (s : _87968 -> Prop) : (term269 _87967 _87968 _35564 f _35565 s) = (term49 _87967 _87968 _35564 f _35565 s).
Proof. exact (TRANS (@lem3386761 _87967 _87968 _35564 f _35565 s) (@lem3386770 _87967 _87968 _35564 f _35565 s)). Qed.
Lemma lem3386772 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3386773 {_87967 _87968 : Type'} (_35564 : _87967) (f : _87968 -> _87967) (_35565 : _87968) (s : _87968 -> Prop) : (term275 _87967 _87968 _35564 f _35565 s) = (term276 _87967 _87968 _35564 f _35565 s).
Proof. exact (MK_COMB (@lem3386772) (@lem3386771 _87967 _87968 _35564 f _35565 s)). Qed.
Lemma lem3386774 {_87967 : Type'} (P : _87967 -> Prop) (_35564 : _87967) : (P _35564) = (P _35564).
Proof. exact (eq_refl (P _35564)). Qed.
Lemma lem3386775 {_87967 _87968 : Type'} (f : _87968 -> _87967) (_35565 : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (_35564 : _87967) : (term266 _87967 _87968 f _35565 s P _35564) = (term277 _87967 _87968 f _35565 s P _35564).
Proof. exact (MK_COMB (@lem3386773 _87967 _87968 _35564 f _35565 s) (@lem3386774 _87967 P _35564)). Qed.
Lemma lem3386776 {_87967 _87968 : Type'} (f : _87968 -> _87967) (_35565 : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (_35564 : _87967) : (term262 _87967 _87968 P _35564 f _35565 s) = (term277 _87967 _87968 f _35565 s P _35564).
Proof. exact (TRANS (@lem3386758 _87967 _87968 f _35565 s P _35564) (@lem3386775 _87967 _87968 f _35565 s P _35564)). Qed.
Lemma lem3386778 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : term278 _87967 _87968 f x s.
Proof. exact (conj (@lem3386670 _87967 _87968 f x) (@lem3386677 _87967 _87968 s P f x h1)). Qed.
Lemma lem3386780 {_87967 _87968 : Type'} (_35565 : _87968) (_35564 : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : term277 _87967 _87968 f _35565 s P _35564.
Proof. exact (EQ_MP (@lem3386776 _87967 _87968 f _35565 s P _35564) (@lem3386755 _87967 _87968 _35564 _35565 s P f x h1)). Qed.
Lemma lem3386781 {_87967 _87968 : Type'} (_35565 : _87968) (_35564 : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : term277 _87967 _87968 f _35565 s P _35564.
Proof. exact (@lem3386780 _87967 _87968 _35565 _35564 s P f x h1). Qed.
Lemma lem3386782 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : term279 _87967 _87968 s P f x.
Proof. exact (@lem3386781 _87967 _87968 x (f x) s P f x h1). Qed.
Lemma lem3386785 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : term85 _87967 _87968 P f x.
Proof. exact (@lem3386782 _87967 _87968 s P f x h1 (@lem3386778 _87967 _87968 s P f x h1)). Qed.
Lemma lem3386786 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : term280 _87967 _87968 P f x.
Proof. exact (fun h0 : term248 _87967 _87968 P f x => @lem3386785 _87967 _87968 s P f x h1). Qed.
Lemma lem3386788 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3386789 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term280 _87967 _87968 P f x) = (term85 _87967 _87968 P f x).
Proof. exact (@lem3386788 (term85 _87967 _87968 P f x)). Qed.
Lemma lem3386790 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : term85 _87967 _87968 P f x.
Proof. exact (EQ_MP (@lem3386789 _87967 _87968 P f x) (@lem3386786 _87967 _87968 s P f x h1)). Qed.
Lemma lem3386793 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3386795 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) : (term248 _87967 _87968 P f x) = (term281 _87967 _87968 P f x).
Proof. exact (@lem3386793 (term85 _87967 _87968 P f x)). Qed.
Lemma lem3386798 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : term281 _87967 _87968 P f x.
Proof. exact (EQ_MP (@lem3386795 _87967 _87968 P f x) (@lem3386549 _87967 _87968 s P f x h1)). Qed.
Lemma lem3386801 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : False.
Proof. exact (@lem3386798 _87967 _87968 s P f x h1 (@lem3386790 _87967 _87968 s P f x h1)). Qed.
Lemma lem3386802 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : term282.
Proof. exact (fun h0 : ~ False => @lem3386801 _87967 _87968 s P f x h1). Qed.
Lemma lem3386804 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3386805 : term282 = False.
Proof. exact (@lem3386804 False). Qed.
Lemma lem3386806 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (x : _87968) (h1 : term118 _87967 _87968 s P f x) : False.
Proof. exact (EQ_MP (@lem3386805) (@lem3386802 _87967 _87968 s P f x h1)). Qed.
Lemma lem3386808 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : @IN _87968 x' s.
Proof. exact (proj2 (@lem3386441 _87967 _87968 x' y s P f h1)). Qed.
Lemma lem3386809 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : term257 _87968 x' s.
Proof. exact (fun h0 : term247 _87968 x' s => @lem3386808 _87967 _87968 x' y s P f h1). Qed.
Lemma lem3386811 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3386812 {_87968 : Type'} (x' : _87968) (s : _87968 -> Prop) : (term257 _87968 x' s) = (@IN _87968 x' s).
Proof. exact (@lem3386811 (@IN _87968 x' s)). Qed.
Lemma lem3386813 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : @IN _87968 x' s.
Proof. exact (EQ_MP (@lem3386812 _87968 x' s) (@lem3386809 _87967 _87968 x' y s P f h1)). Qed.
Lemma lem3386819 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3386820 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (_35566 : _87968) (s : _87968 -> Prop) : (term86 _87967 _87968 s P f _35566) = (term283 _87967 _87968 P f _35566 s).
Proof. exact (@lem3386819 (term85 _87967 _87968 P f _35566) (term247 _87968 _35566 s)). Qed.
Lemma lem3386826 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3386827 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (_35566 : _87968) (s : _87968 -> Prop) : (term284 _87967 _87968 s P f _35566) = (term285 _87967 _87968 P f _35566 s).
Proof. exact (MK_COMB (@lem3386826) (@lem3386820 _87967 _87968 P f _35566 s)). Qed.
Lemma lem3386833 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (_35566 : _87968) (s : _87968 -> Prop) : (term283 _87967 _87968 P f _35566 s) = (term283 _87967 _87968 P f _35566 s).
Proof. exact (eq_refl (term283 _87967 _87968 P f _35566 s)). Qed.
Lemma lem3386834 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (_35566 : _87968) (s : _87968 -> Prop) : ((term86 _87967 _87968 s P f _35566) = (term283 _87967 _87968 P f _35566 s)) = ((term283 _87967 _87968 P f _35566 s) = (term283 _87967 _87968 P f _35566 s)).
Proof. exact (MK_COMB (@lem3386827 _87967 _87968 P f _35566 s) (@lem3386833 _87967 _87968 P f _35566 s)). Qed.
Lemma lem3386836 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3386837 (x : Prop) : (x = x) = True.
Proof. exact (@lem3386836 Prop x). Qed.
Lemma lem3386838 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (_35566 : _87968) (s : _87968 -> Prop) : ((term283 _87967 _87968 P f _35566 s) = (term283 _87967 _87968 P f _35566 s)) = True.
Proof. exact (@lem3386837 (term283 _87967 _87968 P f _35566 s)). Qed.
Lemma lem3386839 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (_35566 : _87968) (s : _87968 -> Prop) : ((term86 _87967 _87968 s P f _35566) = (term283 _87967 _87968 P f _35566 s)) = True.
Proof. exact (TRANS (@lem3386834 _87967 _87968 P f _35566 s) (@lem3386838 _87967 _87968 P f _35566 s)). Qed.
Lemma lem3386840 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (_35566 : _87968) (s : _87968 -> Prop) : True = ((term86 _87967 _87968 s P f _35566) = (term283 _87967 _87968 P f _35566 s)).
Proof. exact (SYM (@lem3386839 _87967 _87968 P f _35566 s)). Qed.
Lemma lem3386841 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (_35566 : _87968) (s : _87968 -> Prop) : (term86 _87967 _87968 s P f _35566) = (term283 _87967 _87968 P f _35566 s).
Proof. exact (EQ_MP (@lem3386840 _87967 _87968 P f _35566 s) (@lem0)). Qed.
Lemma lem3386842 {_87967 _87968 : Type'} (_35566 : _87968) (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : term283 _87967 _87968 P f _35566 s.
Proof. exact (EQ_MP (@lem3386841 _87967 _87968 P f _35566 s) (@lem3386589 _87967 _87968 _35566 x' y s P f h1)). Qed.
Lemma lem3386844 (b : Prop) (a : Prop) : (a \/ b) = (term265 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3386845 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (_35566 : _87968) : (term283 _87967 _87968 P f _35566 s) = (term286 _87967 _87968 s P f _35566).
Proof. exact (@lem3386844 (term247 _87968 _35566 s) (term85 _87967 _87968 P f _35566)). Qed.
Lemma lem3386847 (a : Prop) : (term42 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3386848 {_87968 : Type'} (_35566 : _87968) (s : _87968 -> Prop) : (term274 _87968 _35566 s) = (@IN _87968 _35566 s).
Proof. exact (@lem3386847 (@IN _87968 _35566 s)). Qed.
Lemma lem3386849 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3386850 {_87968 : Type'} (_35566 : _87968) (s : _87968 -> Prop) : (term287 _87968 _35566 s) = (term288 _87968 _35566 s).
Proof. exact (MK_COMB (@lem3386849) (@lem3386848 _87968 _35566 s)). Qed.
Lemma lem3386851 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (_35566 : _87968) : (term85 _87967 _87968 P f _35566) = (term85 _87967 _87968 P f _35566).
Proof. exact (eq_refl (term85 _87967 _87968 P f _35566)). Qed.
Lemma lem3386852 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (_35566 : _87968) : (term286 _87967 _87968 s P f _35566) = (term47 _87967 _87968 s P f _35566).
Proof. exact (MK_COMB (@lem3386850 _87968 _35566 s) (@lem3386851 _87967 _87968 P f _35566)). Qed.
Lemma lem3386853 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (_35566 : _87968) : (term283 _87967 _87968 P f _35566 s) = (term47 _87967 _87968 s P f _35566).
Proof. exact (TRANS (@lem3386845 _87967 _87968 s P f _35566) (@lem3386852 _87967 _87968 s P f _35566)). Qed.
Lemma lem3386856 {_87967 _87968 : Type'} (_35566 : _87968) (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : term47 _87967 _87968 s P f _35566.
Proof. exact (EQ_MP (@lem3386853 _87967 _87968 s P f _35566) (@lem3386842 _87967 _87968 _35566 x' y s P f h1)). Qed.
Lemma lem3386857 {_87967 _87968 : Type'} (_35566 : _87968) (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : term47 _87967 _87968 s P f _35566.
Proof. exact (@lem3386856 _87967 _87968 _35566 x' y s P f h1). Qed.
Lemma lem3386858 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : term47 _87967 _87968 s P f x'.
Proof. exact (@lem3386857 _87967 _87968 x' x' y s P f h1). Qed.
Lemma lem3386861 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : term85 _87967 _87968 P f x'.
Proof. exact (@lem3386858 _87967 _87968 x' y s P f h1 (@lem3386813 _87967 _87968 x' y s P f h1)). Qed.
Lemma lem3386862 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : term280 _87967 _87968 P f x'.
Proof. exact (fun h0 : term248 _87967 _87968 P f x' => @lem3386861 _87967 _87968 x' y s P f h1). Qed.
Lemma lem3386864 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3386865 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (x' : _87968) : (term280 _87967 _87968 P f x') = (term85 _87967 _87968 P f x').
Proof. exact (@lem3386864 (term85 _87967 _87968 P f x')). Qed.
Lemma lem3386866 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : term85 _87967 _87968 P f x'.
Proof. exact (EQ_MP (@lem3386865 _87967 _87968 P f x') (@lem3386862 _87967 _87968 x' y s P f h1)). Qed.
Lemma lem3386869 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3386871 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (x' : _87968) : (term248 _87967 _87968 P f x') = (term281 _87967 _87968 P f x').
Proof. exact (@lem3386869 (term85 _87967 _87968 P f x')). Qed.
Lemma lem3386874 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : term281 _87967 _87968 P f x'.
Proof. exact (EQ_MP (@lem3386871 _87967 _87968 P f x') (@lem3386602 _87967 _87968 x' y s P f h1)). Qed.
Lemma lem3386877 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : False.
Proof. exact (@lem3386874 _87967 _87968 x' y s P f h1 (@lem3386866 _87967 _87968 x' y s P f h1)). Qed.
Lemma lem3386878 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : term282.
Proof. exact (fun h0 : ~ False => @lem3386877 _87967 _87968 x' y s P f h1). Qed.
Lemma lem3386880 (p : Prop) : (term256 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3386881 : term282 = False.
Proof. exact (@lem3386880 False). Qed.
Lemma lem3386883 {_87967 _87968 : Type'} (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term169 _87967 _87968 x' y s P f) : False.
Proof. exact (EQ_MP (@lem3386881) (@lem3386878 _87967 _87968 x' y s P f h1)). Qed.
Lemma lem3386884 {_87967 _87968 : Type'} (x : _87968) (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term215 _87967 _87968 x x' y s P f) : False.
Proof. exact (or_elim (@lem3386431 _87967 _87968 x x' y s P f h1) (fun h0 : term118 _87967 _87968 s P f x => @lem3386806 _87967 _87968 s P f x h0) (fun h0 : term169 _87967 _87968 x' y s P f => @lem3386883 _87967 _87968 x' y s P f h0)). Qed.
Lemma lem3386885 {_87967 _87968 : Type'} (x : _87968) (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term215 _87967 _87968 x x' y s P f) : (term215 _87967 _87968 x x' y s P f) = False.
Proof. exact (prop_ext (fun h2 : term215 _87967 _87968 x x' y s P f => @lem3386884 _87967 _87968 x x' y s P f h1) (fun h2 : False => @lem3386431 _87967 _87968 x x' y s P f h1)). Qed.
Lemma lem3386886 {_87967 _87968 : Type'} (x : _87968) (x' : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term215 _87967 _87968 x x' y s P f) : False.
Proof. exact (EQ_MP (@lem3386885 _87967 _87968 x x' y s P f h1) (@lem3386431 _87967 _87968 x x' y s P f h1)). Qed.
Lemma lem3386887 {_87967 _87968 : Type'} (x : _87968) (y : _87967) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term218 _87967 _87968 x y s P f) : False.
Proof. exact (ex_elim (@lem3386333 _87967 _87968 x y s P f h1) (fun x' : _87968 => fun h0 : term217 _87967 _87968 x y s P f x' => @lem3386886 _87967 _87968 x x' y s P f h0)). Qed.
Lemma lem3386888 {_87967 _87968 : Type'} (x : _87968) (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term220 _87967 _87968 x s P f) : False.
Proof. exact (ex_elim (@lem3386332 _87967 _87968 x s P f h1) (fun y : _87967 => fun h0 : term219 _87967 _87968 x s P f y => @lem3386887 _87967 _87968 x y s P f h0)). Qed.
Lemma lem3386889 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term52 _87967 _87968 s P f) : False.
Proof. exact (ex_elim (@lem3386331 _87967 _87968 s P f h1) (fun x : _87968 => fun h0 : term221 _87967 _87968 s P f x => @lem3386888 _87967 _87968 x s P f h0)). Qed.
Lemma lem3386890 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term52 _87967 _87968 s P f) : (term52 _87967 _87968 s P f) = False.
Proof. exact (prop_ext (fun h2 : term52 _87967 _87968 s P f => @lem3386889 _87967 _87968 s P f h1) (fun h2 : False => @lem3385785 _87967 _87968 s P f h1)). Qed.
Lemma lem3386891 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) (h1 : term52 _87967 _87968 s P f) : False.
Proof. exact (EQ_MP (@lem3386890 _87967 _87968 s P f h1) (@lem3385785 _87967 _87968 s P f h1)). Qed.
Lemma lem3386892 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : term51 _87967 _87968 s P f.
Proof. exact (fun h0 : term52 _87967 _87968 s P f => @lem3386891 _87967 _87968 s P f h0). Qed.
Lemma lem3386893 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term23 _87967 _87968 f s P) = (term26 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem3385784 _87967 _87968 s P f) (@lem3386892 _87967 _87968 s P f)). Qed.
Lemma lem3386898 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term30 _87967 _87968 P f.
Proof. exact (fun s : _87968 -> Prop => @lem3386893 _87967 _87968 s P f). Qed.
Lemma lem3386903 {_87967 _87968 : Type'} (P : _87967 -> Prop) : term34 _87967 _87968 P.
Proof. exact (fun f : _87968 -> _87967 => @lem3386898 _87967 _87968 P f). Qed.
Lemma lem3386908 {_87967 _87968 : Type'} : term46 _87967 _87968.
Proof. exact (fun P : _87967 -> Prop => @lem3386903 _87967 _87968 P). Qed.
Lemma lem3386909 {_87967 _87968 : Type'} : term45 _87967 _87968.
Proof. exact (EQ_MP (@lem3385780 _87967 _87968) (@lem3386908 _87967 _87968)). Qed.
Lemma lem3386910 {_87967 _87968 : Type'} (P : _87967 -> Prop) : term289 _87967 _87968 P.
Proof. exact (@lem3386909 _87967 _87968 P). Qed.
Lemma lem3386911 {_87967 _87968 : Type'} (P : _87967 -> Prop) : (term289 _87967 _87968 P) = (term36 _87967 _87968 P).
Proof. exact (eq_refl (term289 _87967 _87968 P)). Qed.
Lemma lem3386912 {_87967 _87968 : Type'} (P : _87967 -> Prop) : term36 _87967 _87968 P.
Proof. exact (EQ_MP (@lem3386911 _87967 _87968 P) (@lem3386910 _87967 _87968 P)). Qed.
Lemma lem3386914 {_87967 _87968 : Type'} (P : _87967 -> Prop) : term36 _87967 _87968 P.
Proof. exact (@lem3385607 _87967 _87968 P (@lem3386912 _87967 _87968 P)). Qed.
Lemma lem3386915 {_87967 _87968 : Type'} (P : _87967 -> Prop) (h1 : term37 _87967 _87968 P) : False.
Proof. exact (@lem3386914 _87967 _87968 P (@lem3385591 _87967 _87968 P h1)). Qed.
Lemma lem3386916 {_87967 _87968 : Type'} (P : _87967 -> Prop) (h1 : term37 _87967 _87968 P) : (term37 _87967 _87968 P) = False.
Proof. exact (prop_ext (fun h2 : term37 _87967 _87968 P => @lem3386915 _87967 _87968 P h1) (fun h2 : False => @lem3385591 _87967 _87968 P h1)). Qed.
Lemma lem3386917 {_87967 _87968 : Type'} (P : _87967 -> Prop) (h1 : term37 _87967 _87968 P) : False.
Proof. exact (EQ_MP (@lem3386916 _87967 _87968 P h1) (@lem3385591 _87967 _87968 P h1)). Qed.
Lemma lem3386918 {_87967 _87968 : Type'} (P : _87967 -> Prop) : term36 _87967 _87968 P.
Proof. exact (fun h0 : term37 _87967 _87968 P => @lem3386917 _87967 _87968 P h0). Qed.
Lemma lem3386919 {_87967 _87968 : Type'} (P : _87967 -> Prop) : term34 _87967 _87968 P.
Proof. exact (EQ_MP (@lem3385590 _87967 _87968 P) (@lem3386918 _87967 _87968 P)). Qed.
Lemma lem3386920 {_87967 _87968 : Type'} (P : _87967 -> Prop) : term33 _87967 _87968 P.
Proof. exact (EQ_MP (@lem3385586 _87967 _87968 P) (@lem3386919 _87967 _87968 P)). Qed.
