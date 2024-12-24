Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PAIRWISE_SING_term_abbrevs.
Require Import IN_SING_spec.
Require Import pairwise_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm1856_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem4794510 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem4794511 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem4794512 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem4794511 A x) (@lem4794510 A x)). Qed.
Lemma lem4794513 {A : Type'} (x : A) (y : A) : term2 A x y.
Proof. exact (@lem4794512 A x y). Qed.
Lemma lem4794514 {A : Type'} (x : A) (y : A) : (term2 A x y) = ((term3 A x y) = (x = y)).
Proof. exact (eq_refl (term2 A x y)). Qed.
Lemma lem4794516 {_110510 : Type'} (s : _110510 -> Prop) : term4 _110510 s.
Proof. exact (@lem4794393 _110510 s). Qed.
Lemma lem4794517 {_110510 : Type'} (s : _110510 -> Prop) : (term4 _110510 s) = (term5 _110510 s).
Proof. exact (eq_refl (term4 _110510 s)). Qed.
Lemma lem4794518 {_110510 : Type'} (s : _110510 -> Prop) : term5 _110510 s.
Proof. exact (EQ_MP (@lem4794517 _110510 s) (@lem4794516 _110510 s)). Qed.
Lemma lem4794519 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : term6 _110510 s r.
Proof. exact (@lem4794518 _110510 s r). Qed.
Lemma lem4794520 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (term6 _110510 s r) = ((@pairwise _110510 r s) = (term7 _110510 s r)).
Proof. exact (eq_refl (term6 _110510 s r)). Qed.
Lemma lem4794531 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem4794532 {_110540 : Type'} (r : type1402 _110540) (x : _110540) : ((term8 _110540 r x) = True) = (term8 _110540 r x).
Proof. exact (@lem4794531 (term8 _110540 r x)). Qed.
Lemma lem4794534 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (@pairwise _110510 r s) = (term7 _110510 s r).
Proof. exact (EQ_MP (@lem4794520 _110510 s r) (@lem4794519 _110510 s r)). Qed.
Lemma lem4794535 {_110540 : Type'} (s : _110540 -> Prop) (r : type1402 _110540) : (@pairwise _110540 r s) = (term7 _110540 s r).
Proof. exact (@lem4794534 _110540 s r). Qed.
Lemma lem4794536 {_110540 : Type'} (x : _110540) (r : type1402 _110540) : (term8 _110540 r x) = (term9 _110540 x r).
Proof. exact (@lem4794535 _110540 (@INSERT _110540 x (@EMPTY _110540)) r). Qed.
Lemma lem4794541 {_110540 : Type'} (x : _110540) (r : type1402 _110540) : ((term8 _110540 r x) = True) = (term9 _110540 x r).
Proof. exact (TRANS (@lem4794532 _110540 r x) (@lem4794536 _110540 x r)). Qed.
Lemma lem4794551 {A : Type'} (x : A) (y : A) : (term3 A x y) = (x = y).
Proof. exact (EQ_MP (@lem4794514 A x y) (@lem4794513 A x y)). Qed.
Lemma lem4794552 {_110540 : Type'} (x : _110540) (y : _110540) : (term3 _110540 x y) = (x = y).
Proof. exact (@lem4794551 _110540 x y). Qed.
Lemma lem4794553 {_110540 : Type'} (x' : _110540) (x : _110540) : (term3 _110540 x' x) = (x' = x).
Proof. exact (@lem4794552 _110540 x' x). Qed.
Lemma lem4794556 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4794557 {_110540 : Type'} (x' : _110540) (x : _110540) : (term10 _110540 x' x) = (term11 _110540 x' x).
Proof. exact (MK_COMB (@lem4794556) (@lem4794553 _110540 x' x)). Qed.
Lemma lem4794561 {A : Type'} (x : A) (y : A) : (term3 A x y) = (x = y).
Proof. exact (EQ_MP (@lem4794514 A x y) (@lem4794513 A x y)). Qed.
Lemma lem4794562 {_110540 : Type'} (x : _110540) (y : _110540) : (term3 _110540 x y) = (x = y).
Proof. exact (@lem4794561 _110540 x y). Qed.
Lemma lem4794563 {_110540 : Type'} (y : _110540) (x : _110540) : (term3 _110540 y x) = (y = x).
Proof. exact (@lem4794562 _110540 y x). Qed.
Lemma lem4794566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4794567 {_110540 : Type'} (y : _110540) (x : _110540) : (term10 _110540 y x) = (term11 _110540 y x).
Proof. exact (MK_COMB (@lem4794566) (@lem4794563 _110540 y x)). Qed.
Lemma lem4794570 {_110540 : Type'} (x' : _110540) (y : _110540) : (term12 _110540 x' y) = (term12 _110540 x' y).
Proof. exact (eq_refl (term12 _110540 x' y)). Qed.
Lemma lem4794571 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) : (term13 _110540 x x' y) = (term14 _110540 x x' y).
Proof. exact (MK_COMB (@lem4794567 _110540 y x) (@lem4794570 _110540 x' y)). Qed.
Lemma lem4794574 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) : (term15 _110540 x x' y) = (term16 _110540 x x' y).
Proof. exact (MK_COMB (@lem4794557 _110540 x' x) (@lem4794571 _110540 x x' y)). Qed.
Lemma lem4794577 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4794578 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) : (term17 _110540 x x' y) = (term18 _110540 x x' y).
Proof. exact (MK_COMB (@lem4794577) (@lem4794574 _110540 x x' y)). Qed.
Lemma lem4794579 {_110540 : Type'} (r : type1402 _110540) (x' : _110540) (y : _110540) : (r x' y) = (r x' y).
Proof. exact (eq_refl (r x' y)). Qed.
Lemma lem4794580 {_110540 : Type'} (x : _110540) (r : type1402 _110540) (x' : _110540) (y : _110540) : (term19 _110540 x r x' y) = (term20 _110540 x r x' y).
Proof. exact (MK_COMB (@lem4794578 _110540 x x' y) (@lem4794579 _110540 r x' y)). Qed.
Lemma lem4794583 {_110540 : Type'} (x : _110540) (r : type1402 _110540) (x' : _110540) : (term21 _110540 x r x') = (term22 _110540 x r x').
Proof. exact (fun_ext (fun y : _110540 => @lem4794580 _110540 x r x' y)). Qed.
Lemma lem4794584 {_110540 : Type'} : (@all _110540) = (@all _110540).
Proof. exact (eq_refl (@all _110540)). Qed.
Lemma lem4794585 {_110540 : Type'} (x : _110540) (r : type1402 _110540) (x' : _110540) : (term23 _110540 x r x') = (term24 _110540 x r x').
Proof. exact (MK_COMB (@lem4794584 _110540) (@lem4794583 _110540 x r x')). Qed.
Lemma lem4794590 {_110540 : Type'} (x : _110540) (r : type1402 _110540) : (term25 _110540 x r) = (term26 _110540 x r).
Proof. exact (fun_ext (fun x' : _110540 => @lem4794585 _110540 x r x')). Qed.
Lemma lem4794591 {_110540 : Type'} : (@all _110540) = (@all _110540).
Proof. exact (eq_refl (@all _110540)). Qed.
Lemma lem4794592 {_110540 : Type'} (x : _110540) (r : type1402 _110540) : (term9 _110540 x r) = (term27 _110540 x r).
Proof. exact (MK_COMB (@lem4794591 _110540) (@lem4794590 _110540 x r)). Qed.
Lemma lem4794597 {_110540 : Type'} (x : _110540) (r : type1402 _110540) : ((term8 _110540 r x) = True) = (term27 _110540 x r).
Proof. exact (TRANS (@lem4794541 _110540 x r) (@lem4794592 _110540 x r)). Qed.
Lemma lem4794598 {_110540 : Type'} (r : type1402 _110540) : (term28 _110540 r) = (term29 _110540 r).
Proof. exact (fun_ext (fun x : _110540 => @lem4794597 _110540 x r)). Qed.
Lemma lem4794599 {_110540 : Type'} : (@all _110540) = (@all _110540).
Proof. exact (eq_refl (@all _110540)). Qed.
Lemma lem4794600 {_110540 : Type'} (r : type1402 _110540) : (term30 _110540 r) = (term31 _110540 r).
Proof. exact (MK_COMB (@lem4794599 _110540) (@lem4794598 _110540 r)). Qed.
Lemma lem4794605 {_110540 : Type'} : (term32 _110540) = (term33 _110540).
Proof. exact (fun_ext (fun r : type1402 _110540 => @lem4794600 _110540 r)). Qed.
Lemma lem4794606 {_110540 : Type'} : (@all (_110540 -> _110540 -> Prop)) = (@all (_110540 -> _110540 -> Prop)).
Proof. exact (eq_refl (@all (_110540 -> _110540 -> Prop))). Qed.
Lemma lem4794607 {_110540 : Type'} : (term34 _110540) = (term35 _110540).
Proof. exact (MK_COMB (@lem4794606 _110540) (@lem4794605 _110540)). Qed.
Lemma lem4794612 {_110540 : Type'} : (term35 _110540) = (term34 _110540).
Proof. exact (SYM (@lem4794607 _110540)). Qed.
Lemma lem4794614 (p : Prop) : p = (term36 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4794615 {_110540 : Type'} : (term35 _110540) = (term37 _110540).
Proof. exact (@lem4794614 (term35 _110540)). Qed.
Lemma lem4794616 {_110540 : Type'} : (term37 _110540) = (term35 _110540).
Proof. exact (SYM (@lem4794615 _110540)). Qed.
Lemma lem4794617 {_110540 : Type'} (h1 : term38 _110540) : term38 _110540.
Proof. exact (h1). Qed.
Lemma lem4794620 {_110540 : Type'} (h1 : term37 _110540) : term37 _110540.
Proof. exact (h1). Qed.
Lemma lem4794621 {_110540 : Type'} : term39 _110540.
Proof. exact (fun h0 : term37 _110540 => @lem4794620 _110540 h0). Qed.
Lemma lem4794622 {_110540 : Type'} (h1 : term39 _110540) : term39 _110540.
Proof. exact (h1). Qed.
Lemma lem4794623 {_110540 : Type'} (h1 : term37 _110540) : term37 _110540.
Proof. exact (h1). Qed.
Lemma lem4794624 {_110540 : Type'} (h1 : term37 _110540) (h2 : term39 _110540) : term37 _110540.
Proof. exact (@lem4794622 _110540 h2 (@lem4794623 _110540 h1)). Qed.
Lemma lem4794625 {_110540 : Type'} (h1 : term37 _110540) : term40 _110540.
Proof. exact (fun h0 : term39 _110540 => @lem4794624 _110540 h1 h0). Qed.
Lemma lem4794626 {_110540 : Type'} (h1 : term39 _110540) : term39 _110540.
Proof. exact (h1). Qed.
Lemma lem4794627 {_110540 : Type'} (h1 : term37 _110540) (h2 : term39 _110540) : term37 _110540.
Proof. exact (@lem4794625 _110540 h1 (@lem4794626 _110540 h2)). Qed.
Lemma lem4794628 {_110540 : Type'} (h1 : term39 _110540) : term39 _110540.
Proof. exact (fun h0 : term37 _110540 => @lem4794627 _110540 h0 h1). Qed.
Lemma lem4794629 {_110540 : Type'} : term41 _110540.
Proof. exact (fun h0 : term39 _110540 => @lem4794628 _110540 h0). Qed.
Lemma lem4794632 {_110540 : Type'} : term39 _110540.
Proof. exact (@lem4794629 _110540 (@lem4794621 _110540)). Qed.
Lemma lem4794633 {_110540 : Type'} : term39 _110540.
Proof. exact (@lem4794632 _110540). Qed.
Lemma lem4794635 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4794636 {_110540 : Type'} : (term37 _110540) = (term42 _110540).
Proof. exact (@lem4794635 (term38 _110540)). Qed.
Lemma lem4794638 (t : Prop) : (term43 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4794639 {_110540 : Type'} : (term42 _110540) = (term35 _110540).
Proof. exact (@lem4794638 (term35 _110540)). Qed.
Lemma lem4794666 {_110540 : Type'} : (term37 _110540) = (term35 _110540).
Proof. exact (TRANS (@lem4794636 _110540) (@lem4794639 _110540)). Qed.
Lemma lem4794681 {_110540 : Type'} (x : _110540) (r : type1402 _110540) (x' : _110540) (y : _110540) : (term20 _110540 x r x' y) = (term20 _110540 x r x' y).
Proof. exact (eq_refl (term20 _110540 x r x' y)). Qed.
Lemma lem4794682 {_110540 : Type'} (x : _110540) (r : type1402 _110540) (x' : _110540) : (term22 _110540 x r x') = (term22 _110540 x r x').
Proof. exact (fun_ext (fun y : _110540 => @lem4794681 _110540 x r x' y)). Qed.
Lemma lem4794683 {_110540 : Type'} : (@all _110540) = (@all _110540).
Proof. exact (eq_refl (@all _110540)). Qed.
Lemma lem4794684 {_110540 : Type'} (x : _110540) (r : type1402 _110540) (x' : _110540) : (term24 _110540 x r x') = (term24 _110540 x r x').
Proof. exact (MK_COMB (@lem4794683 _110540) (@lem4794682 _110540 x r x')). Qed.
Lemma lem4794685 {_110540 : Type'} (x : _110540) (r : type1402 _110540) : (term26 _110540 x r) = (term26 _110540 x r).
Proof. exact (fun_ext (fun x' : _110540 => @lem4794684 _110540 x r x')). Qed.
Lemma lem4794686 {_110540 : Type'} : (@all _110540) = (@all _110540).
Proof. exact (eq_refl (@all _110540)). Qed.
Lemma lem4794687 {_110540 : Type'} (x : _110540) (r : type1402 _110540) : (term27 _110540 x r) = (term27 _110540 x r).
Proof. exact (MK_COMB (@lem4794686 _110540) (@lem4794685 _110540 x r)). Qed.
Lemma lem4794688 {_110540 : Type'} (r : type1402 _110540) : (term29 _110540 r) = (term29 _110540 r).
Proof. exact (fun_ext (fun x : _110540 => @lem4794687 _110540 x r)). Qed.
Lemma lem4794689 {_110540 : Type'} : (@all _110540) = (@all _110540).
Proof. exact (eq_refl (@all _110540)). Qed.
Lemma lem4794690 {_110540 : Type'} (r : type1402 _110540) : (term31 _110540 r) = (term31 _110540 r).
Proof. exact (MK_COMB (@lem4794689 _110540) (@lem4794688 _110540 r)). Qed.
Lemma lem4794691 {_110540 : Type'} : (term33 _110540) = (term33 _110540).
Proof. exact (fun_ext (fun r : type1402 _110540 => @lem4794690 _110540 r)). Qed.
Lemma lem4794692 {_110540 : Type'} : (@all (_110540 -> _110540 -> Prop)) = (@all (_110540 -> _110540 -> Prop)).
Proof. exact (eq_refl (@all (_110540 -> _110540 -> Prop))). Qed.
Lemma lem4794693 {_110540 : Type'} : (term35 _110540) = (term35 _110540).
Proof. exact (MK_COMB (@lem4794692 _110540) (@lem4794691 _110540)). Qed.
Lemma lem4794726 {_110540 : Type'} : (term37 _110540) = (term35 _110540).
Proof. exact (TRANS (@lem4794666 _110540) (@lem4794693 _110540)). Qed.
Lemma lem4794727 {_110540 : Type'} : (term35 _110540) = (term37 _110540).
Proof. exact (SYM (@lem4794726 _110540)). Qed.
Lemma lem4794730 (p : Prop) : p = (term36 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4794731 {_110540 : Type'} (r : type1402 _110540) (x' : _110540) (y : _110540) : (r x' y) = (term44 _110540 r x' y).
Proof. exact (@lem4794730 (r x' y)). Qed.
Lemma lem4794732 {_110540 : Type'} (r : type1402 _110540) (x' : _110540) (y : _110540) : (term44 _110540 r x' y) = (r x' y).
Proof. exact (SYM (@lem4794731 _110540 r x' y)). Qed.
Lemma lem4794747 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : term16 _110540 x x' y.
Proof. exact (h1). Qed.
Lemma lem4794777 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : term16 _110540 x x' y.
Proof. exact (h1). Qed.
Lemma lem4794786 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : term14 _110540 x x' y.
Proof. exact (proj2 (@lem4794777 _110540 x x' y h1)). Qed.
Lemma lem4794811 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : y = x.
Proof. exact (proj1 (@lem4794786 _110540 x x' y h1)). Qed.
Lemma lem4794813 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : term12 _110540 x' y.
Proof. exact (proj2 (@lem4794786 _110540 x x' y h1)). Qed.
Lemma lem4794854 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : x' = x.
Proof. exact (proj1 (@lem4794777 _110540 x x' y h1)). Qed.
Lemma lem4794855 {_110540 : Type'} (x' : _110540) : (term45 _110540 x') = (term45 _110540 x').
Proof. exact (eq_refl (term45 _110540 x')). Qed.
Lemma lem4794856 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : (term46 _110540 x' y) = (term46 _110540 x' x).
Proof. exact (MK_COMB (@lem4794855 _110540 x') (@lem4794811 _110540 x x' y h1)). Qed.
Lemma lem4794857 {_110540 : Type'} (x' : _110540) (x : _110540) : (term46 _110540 x' x) = (term12 _110540 x' x).
Proof. exact (eq_refl (term46 _110540 x' x)). Qed.
Lemma lem4794858 {_110540 : Type'} (x' : _110540) (y : _110540) : (term47 _110540 x' y) = (term47 _110540 x' y).
Proof. exact (eq_refl (term47 _110540 x' y)). Qed.
Lemma lem4794859 {_110540 : Type'} (y : _110540) (x' : _110540) (x : _110540) : ((term46 _110540 x' y) = (term46 _110540 x' x)) = ((term46 _110540 x' y) = (term12 _110540 x' x)).
Proof. exact (MK_COMB (@lem4794858 _110540 x' y) (@lem4794857 _110540 x' x)). Qed.
Lemma lem4794860 {_110540 : Type'} (x' : _110540) (y : _110540) : (term46 _110540 x' y) = (term12 _110540 x' y).
Proof. exact (eq_refl (term46 _110540 x' y)). Qed.
Lemma lem4794861 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4794862 {_110540 : Type'} (x' : _110540) (y : _110540) : (term47 _110540 x' y) = (term48 _110540 x' y).
Proof. exact (MK_COMB (@lem4794861) (@lem4794860 _110540 x' y)). Qed.
Lemma lem4794863 {_110540 : Type'} (x' : _110540) (x : _110540) : (term12 _110540 x' x) = (term12 _110540 x' x).
Proof. exact (eq_refl (term12 _110540 x' x)). Qed.
Lemma lem4794864 {_110540 : Type'} (y : _110540) (x' : _110540) (x : _110540) : ((term46 _110540 x' y) = (term12 _110540 x' x)) = ((term12 _110540 x' y) = (term12 _110540 x' x)).
Proof. exact (MK_COMB (@lem4794862 _110540 x' y) (@lem4794863 _110540 x' x)). Qed.
Lemma lem4794865 {_110540 : Type'} (y : _110540) (x' : _110540) (x : _110540) : ((term46 _110540 x' y) = (term46 _110540 x' x)) = ((term12 _110540 x' y) = (term12 _110540 x' x)).
Proof. exact (TRANS (@lem4794859 _110540 y x' x) (@lem4794864 _110540 y x' x)). Qed.
Lemma lem4794866 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : (term12 _110540 x' y) = (term12 _110540 x' x).
Proof. exact (EQ_MP (@lem4794865 _110540 y x' x) (@lem4794856 _110540 x x' y h1)). Qed.
Lemma lem4794867 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : term12 _110540 x' x.
Proof. exact (EQ_MP (@lem4794866 _110540 x x' y h1) (@lem4794813 _110540 x x' y h1)). Qed.
Lemma lem4794895 {_110540 : Type'} (x : _110540) : (term49 _110540 x) = (term49 _110540 x).
Proof. exact (eq_refl (term49 _110540 x)). Qed.
Lemma lem4794896 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : (term50 _110540 x x') = (term51 _110540 x).
Proof. exact (MK_COMB (@lem4794895 _110540 x) (@lem4794854 _110540 x x' y h1)). Qed.
Lemma lem4794897 {_110540 : Type'} (x : _110540) : (term51 _110540 x) = (term52 _110540 x).
Proof. exact (eq_refl (term51 _110540 x)). Qed.
Lemma lem4794898 {_110540 : Type'} (x : _110540) (x' : _110540) : (term53 _110540 x x') = (term53 _110540 x x').
Proof. exact (eq_refl (term53 _110540 x x')). Qed.
Lemma lem4794899 {_110540 : Type'} (x' : _110540) (x : _110540) : ((term50 _110540 x x') = (term51 _110540 x)) = ((term50 _110540 x x') = (term52 _110540 x)).
Proof. exact (MK_COMB (@lem4794898 _110540 x x') (@lem4794897 _110540 x)). Qed.
Lemma lem4794900 {_110540 : Type'} (x' : _110540) (x : _110540) : (term50 _110540 x x') = (term12 _110540 x' x).
Proof. exact (eq_refl (term50 _110540 x x')). Qed.
Lemma lem4794901 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4794902 {_110540 : Type'} (x' : _110540) (x : _110540) : (term53 _110540 x x') = (term48 _110540 x' x).
Proof. exact (MK_COMB (@lem4794901) (@lem4794900 _110540 x' x)). Qed.
Lemma lem4794903 {_110540 : Type'} (x : _110540) : (term52 _110540 x) = (term52 _110540 x).
Proof. exact (eq_refl (term52 _110540 x)). Qed.
Lemma lem4794904 {_110540 : Type'} (x' : _110540) (x : _110540) : ((term50 _110540 x x') = (term52 _110540 x)) = ((term12 _110540 x' x) = (term52 _110540 x)).
Proof. exact (MK_COMB (@lem4794902 _110540 x' x) (@lem4794903 _110540 x)). Qed.
Lemma lem4794905 {_110540 : Type'} (x' : _110540) (x : _110540) : ((term50 _110540 x x') = (term51 _110540 x)) = ((term12 _110540 x' x) = (term52 _110540 x)).
Proof. exact (TRANS (@lem4794899 _110540 x' x) (@lem4794904 _110540 x' x)). Qed.
Lemma lem4794906 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : (term12 _110540 x' x) = (term52 _110540 x).
Proof. exact (EQ_MP (@lem4794905 _110540 x' x) (@lem4794896 _110540 x x' y h1)). Qed.
Lemma lem4794907 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : term52 _110540 x.
Proof. exact (EQ_MP (@lem4794906 _110540 x x' y h1) (@lem4794867 _110540 x x' y h1)). Qed.
Lemma lem4794930 {_110540 : Type'} (x : _110540) : x = x.
Proof. exact (@lem21386 _110540 x). Qed.
Lemma lem4794931 {_110540 : Type'} (x : _110540) : x = x.
Proof. exact (@lem4794930 _110540 x). Qed.
Lemma lem4794932 {_110540 : Type'} (x : _110540) : term54 _110540 x.
Proof. exact (fun h0 : term52 _110540 x => @lem4794931 _110540 x). Qed.
Lemma lem4794934 (p : Prop) : (term55 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4794935 {_110540 : Type'} (x : _110540) : (term54 _110540 x) = (x = x).
Proof. exact (@lem4794934 (x = x)). Qed.
Lemma lem4794936 {_110540 : Type'} (x : _110540) : x = x.
Proof. exact (EQ_MP (@lem4794935 _110540 x) (@lem4794932 _110540 x)). Qed.
Lemma lem4794939 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4794941 {_110540 : Type'} (x : _110540) : (term52 _110540 x) = (term56 _110540 x).
Proof. exact (@lem4794939 (x = x)). Qed.
Lemma lem4794944 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : term56 _110540 x.
Proof. exact (EQ_MP (@lem4794941 _110540 x) (@lem4794907 _110540 x x' y h1)). Qed.
Lemma lem4794947 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : False.
Proof. exact (@lem4794944 _110540 x x' y h1 (@lem4794936 _110540 x)). Qed.
Lemma lem4794948 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : term57.
Proof. exact (fun h0 : ~ False => @lem4794947 _110540 x x' y h1). Qed.
Lemma lem4794950 (p : Prop) : (term55 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4794951 : term57 = False.
Proof. exact (@lem4794950 False). Qed.
Lemma lem4794954 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : False.
Proof. exact (EQ_MP (@lem4794951) (@lem4794948 _110540 x x' y h1)). Qed.
Lemma lem4794955 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : (term16 _110540 x x' y) = False.
Proof. exact (prop_ext (fun h2 : term16 _110540 x x' y => @lem4794954 _110540 x x' y h1) (fun h2 : False => @lem4794777 _110540 x x' y h1)). Qed.
Lemma lem4794956 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : False.
Proof. exact (EQ_MP (@lem4794955 _110540 x x' y h1) (@lem4794777 _110540 x x' y h1)). Qed.
Lemma lem4794957 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : (term16 _110540 x x' y) = False.
Proof. exact (prop_ext (fun h2 : term16 _110540 x x' y => @lem4794956 _110540 x x' y h1) (fun h2 : False => @lem4794747 _110540 x x' y h1)). Qed.
Lemma lem4794958 {_110540 : Type'} (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : False.
Proof. exact (EQ_MP (@lem4794957 _110540 x x' y h1) (@lem4794747 _110540 x x' y h1)). Qed.
Lemma lem4794959 {_110540 : Type'} (r : type1402 _110540) (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : term44 _110540 r x' y.
Proof. exact (fun h0 : term58 _110540 r x' y => @lem4794958 _110540 x x' y h1). Qed.
Lemma lem4794960 {_110540 : Type'} (r : type1402 _110540) (x : _110540) (x' : _110540) (y : _110540) (h1 : term16 _110540 x x' y) : r x' y.
Proof. exact (EQ_MP (@lem4794732 _110540 r x' y) (@lem4794959 _110540 r x x' y h1)). Qed.
Lemma lem4794961 {_110540 : Type'} (x : _110540) (r : type1402 _110540) (x' : _110540) (y : _110540) : term20 _110540 x r x' y.
Proof. exact (fun h0 : term16 _110540 x x' y => @lem4794960 _110540 r x x' y h0). Qed.
Lemma lem4794966 {_110540 : Type'} (x : _110540) (r : type1402 _110540) (x' : _110540) : term24 _110540 x r x'.
Proof. exact (fun y : _110540 => @lem4794961 _110540 x r x' y). Qed.
Lemma lem4794971 {_110540 : Type'} (x : _110540) (r : type1402 _110540) : term27 _110540 x r.
Proof. exact (fun x' : _110540 => @lem4794966 _110540 x r x'). Qed.
Lemma lem4794976 {_110540 : Type'} (r : type1402 _110540) : term31 _110540 r.
Proof. exact (fun x : _110540 => @lem4794971 _110540 x r). Qed.
Lemma lem4794981 {_110540 : Type'} : term35 _110540.
Proof. exact (fun r : type1402 _110540 => @lem4794976 _110540 r). Qed.
Lemma lem4794982 {_110540 : Type'} : term37 _110540.
Proof. exact (EQ_MP (@lem4794727 _110540) (@lem4794981 _110540)). Qed.
Lemma lem4794984 {_110540 : Type'} : term37 _110540.
Proof. exact (@lem4794633 _110540 (@lem4794982 _110540)). Qed.
Lemma lem4794985 {_110540 : Type'} (h1 : term38 _110540) : False.
Proof. exact (@lem4794984 _110540 (@lem4794617 _110540 h1)). Qed.
Lemma lem4794986 {_110540 : Type'} (h1 : term38 _110540) : (term38 _110540) = False.
Proof. exact (prop_ext (fun h2 : term38 _110540 => @lem4794985 _110540 h1) (fun h2 : False => @lem4794617 _110540 h1)). Qed.
Lemma lem4794987 {_110540 : Type'} (h1 : term38 _110540) : False.
Proof. exact (EQ_MP (@lem4794986 _110540 h1) (@lem4794617 _110540 h1)). Qed.
Lemma lem4794988 {_110540 : Type'} : term37 _110540.
Proof. exact (fun h0 : term38 _110540 => @lem4794987 _110540 h0). Qed.
Lemma lem4794989 {_110540 : Type'} : term35 _110540.
Proof. exact (EQ_MP (@lem4794616 _110540) (@lem4794988 _110540)). Qed.
Lemma lem4794990 {_110540 : Type'} : term34 _110540.
Proof. exact (EQ_MP (@lem4794612 _110540) (@lem4794989 _110540)). Qed.
