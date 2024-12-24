Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_CART_UNIV_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import HAS_SIZE_FINITE_IMAGE_spec.
Require Import HAS_SIZE_FUNSPACE_UNIV_spec.
Require Import HAS_SIZE_IMAGE_INJ_spec.
Require Import IN_UNIV_spec.
Require Import SURJECTIVE_IMAGE_EQ_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1157_spec.
Require Import thm129_spec.
Require Import thm137_spec.
Require Import thm16462_spec.
Require Import thm16474_spec.
Require Import thm17362_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1855_spec.
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
Require Import thm21385_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm7614851_spec.
Require Import thm951_spec.
Require Import thm952_spec.
Lemma lem7989585 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem7989586 {A : Type'} (x : A) : (term0 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem7989587 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem7989586 A x) (@lem7989585 A x)). Qed.
Lemma lem7989588 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem7989590 {_88266 _88270 : Type'} (f : _88270 -> _88266) (h1 : term1 _88266 _88270 f) : term1 _88266 _88270 f.
Proof. exact (h1). Qed.
Lemma lem7989591 {_88266 _88270 : Type'} (s : _88270 -> Prop) (f : _88270 -> _88266) (h1 : term1 _88266 _88270 f) : term2 _88266 _88270 f s.
Proof. exact (@lem7989590 _88266 _88270 f h1 s). Qed.
Lemma lem7989592 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) : (term2 _88266 _88270 f s) = (term3 _88266 _88270 f s).
Proof. exact (eq_refl (term2 _88266 _88270 f s)). Qed.
Lemma lem7989593 {_88266 _88270 : Type'} (s : _88270 -> Prop) (f : _88270 -> _88266) (h1 : term1 _88266 _88270 f) : term3 _88266 _88270 f s.
Proof. exact (EQ_MP (@lem7989592 _88266 _88270 f s) (@lem7989591 _88266 _88270 s f h1)). Qed.
Lemma lem7989594 {_88266 _88270 : Type'} (s : _88270 -> Prop) (t : _88266 -> Prop) (f : _88270 -> _88266) (h1 : term1 _88266 _88270 f) : term4 _88266 _88270 f s t.
Proof. exact (@lem7989593 _88266 _88270 s f h1 t). Qed.
Lemma lem7989595 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) : (term4 _88266 _88270 f s t) = (term5 _88266 _88270 f s t).
Proof. exact (eq_refl (term4 _88266 _88270 f s t)). Qed.
Lemma lem7989596 {_88266 _88270 : Type'} (s : _88270 -> Prop) (t : _88266 -> Prop) (f : _88270 -> _88266) (h1 : term1 _88266 _88270 f) : term5 _88266 _88270 f s t.
Proof. exact (EQ_MP (@lem7989595 _88266 _88270 f s t) (@lem7989594 _88266 _88270 s t f h1)). Qed.
Lemma lem7989597 {_88266 _88270 : Type'} (f : _88270 -> _88266) (t : _88266 -> Prop) (s : _88270 -> Prop) (h1 : term6 _88266 _88270 f t s) : term6 _88266 _88270 f t s.
Proof. exact (h1). Qed.
Lemma lem7989598 {_88266 _88270 : Type'} (f : _88270 -> _88266) (t : _88266 -> Prop) (s : _88270 -> Prop) (h1 : term1 _88266 _88270 f) (h2 : term6 _88266 _88270 f t s) : (@IMAGE _88270 _88266 f s) = t.
Proof. exact (@lem7989596 _88266 _88270 s t f h1 (@lem7989597 _88266 _88270 f t s h2)). Qed.
Lemma lem7989599 {_88266 _88270 : Type'} (f : _88270 -> _88266) (t : _88266 -> Prop) (s : _88270 -> Prop) (h1 : term6 _88266 _88270 f t s) : term7 _88266 _88270 f s t.
Proof. exact (fun h0 : term1 _88266 _88270 f => @lem7989598 _88266 _88270 f t s h0 h1). Qed.
Lemma lem7989600 {_88266 _88270 : Type'} (f : _88270 -> _88266) (h1 : term1 _88266 _88270 f) : term1 _88266 _88270 f.
Proof. exact (h1). Qed.
Lemma lem7989601 {_88266 _88270 : Type'} (f : _88270 -> _88266) (t : _88266 -> Prop) (s : _88270 -> Prop) (h1 : term1 _88266 _88270 f) (h2 : term6 _88266 _88270 f t s) : (@IMAGE _88270 _88266 f s) = t.
Proof. exact (@lem7989599 _88266 _88270 f t s h2 (@lem7989600 _88266 _88270 f h1)). Qed.
Lemma lem7989602 {_88266 _88270 : Type'} (s : _88270 -> Prop) (t : _88266 -> Prop) (f : _88270 -> _88266) (h1 : term1 _88266 _88270 f) : term5 _88266 _88270 f s t.
Proof. exact (fun h0 : term6 _88266 _88270 f t s => @lem7989601 _88266 _88270 f t s h1 h0). Qed.
Lemma lem7989603 {_88266 _88270 : Type'} (s : _88270 -> Prop) (f : _88270 -> _88266) (h1 : term1 _88266 _88270 f) : term3 _88266 _88270 f s.
Proof. exact (fun t : _88266 -> Prop => @lem7989602 _88266 _88270 s t f h1). Qed.
Lemma lem7989604 {_88266 _88270 : Type'} (f : _88270 -> _88266) (h1 : term1 _88266 _88270 f) : term1 _88266 _88270 f.
Proof. exact (fun s : _88270 -> Prop => @lem7989603 _88266 _88270 s f h1). Qed.
Lemma lem7989605 {_88266 _88270 : Type'} (f : _88270 -> _88266) : term8 _88266 _88270 f.
Proof. exact (fun h0 : term1 _88266 _88270 f => @lem7989604 _88266 _88270 f h0). Qed.
Lemma lem7989606 {_88266 _88270 : Type'} (f : _88270 -> _88266) : term1 _88266 _88270 f.
Proof. exact (@lem7989605 _88266 _88270 f (@lem3399677 _88266 _88270 f)). Qed.
Lemma lem7989607 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) : term2 _88266 _88270 f s.
Proof. exact (@lem7989606 _88266 _88270 f s). Qed.
Lemma lem7989608 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) : (term2 _88266 _88270 f s) = (term3 _88266 _88270 f s).
Proof. exact (eq_refl (term2 _88266 _88270 f s)). Qed.
Lemma lem7989609 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) : term3 _88266 _88270 f s.
Proof. exact (EQ_MP (@lem7989608 _88266 _88270 f s) (@lem7989607 _88266 _88270 f s)). Qed.
Lemma lem7989610 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) : term4 _88266 _88270 f s t.
Proof. exact (@lem7989609 _88266 _88270 f s t). Qed.
Lemma lem7989611 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) : (term4 _88266 _88270 f s t) = (term5 _88266 _88270 f s t).
Proof. exact (eq_refl (term4 _88266 _88270 f s t)). Qed.
Lemma lem7989613 (a : Prop) (b : Prop) (h1 : term9 a b) : term9 a b.
Proof. exact (h1). Qed.
Lemma lem7989614 (a : Prop) (b : Prop) (h1 : a = b) : a = b.
Proof. exact (h1). Qed.
Lemma lem7989615 (a : Prop) (b : Prop) (h1 : a = b) (h2 : term9 a b) : a -> b.
Proof. exact (@lem7989613 a b h2 (@lem7989614 a b h1)). Qed.
Lemma lem7989616 (a : Prop) (b : Prop) (h1 : a = b) : term10 a b.
Proof. exact (fun h0 : term9 a b => @lem7989615 a b h1 h0). Qed.
Lemma lem7989617 (a : Prop) (b : Prop) (h1 : term9 a b) : term9 a b.
Proof. exact (h1). Qed.
Lemma lem7989618 (a : Prop) (b : Prop) (h1 : a = b) (h2 : term9 a b) : a -> b.
Proof. exact (@lem7989616 a b h1 (@lem7989617 a b h2)). Qed.
Lemma lem7989619 (a : Prop) (b : Prop) (h1 : term9 a b) : term9 a b.
Proof. exact (fun h0 : a = b => @lem7989618 a b h0 h1). Qed.
Lemma lem7989620 (a : Prop) (b : Prop) : term11 a b.
Proof. exact (fun h0 : term9 a b => @lem7989619 a b h0). Qed.
Lemma lem7989632 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem7989633 {A : Type'} (x : A) : (term0 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem7989634 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem7989633 A x) (@lem7989632 A x)). Qed.
Lemma lem7989635 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem7989650 (q : Prop) (p : Prop) (r : Prop) : (term12 p q r) = (term13 q p r).
Proof. exact (EQ_MP (@lem952 q p r) (@lem951 p q r)). Qed.
Lemma lem7989651 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term14 A B f s n) = (term15 A B f s n).
Proof. exact (@lem7989650 (@HAS_SIZE A s n) (term16 A B s f) (term17 A B f s n)). Qed.
Lemma lem7989665 (q : Prop) (p : Prop) (r : Prop) : (term12 p q r) = (term13 q p r).
Proof. exact (EQ_MP (@lem952 q p r) (@lem951 p q r)). Qed.
Lemma lem7989666 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term18 A B s f x y) = (term19 A B f s x y).
Proof. exact (@lem7989665 (term20 A B s x f y) (@IN A x s) (x = y)). Qed.
Lemma lem7989668 (q : Prop) (p : Prop) (r : Prop) : (term12 p q r) = (term13 q p r).
Proof. exact (EQ_MP (@lem952 q p r) (@lem951 p q r)). Qed.
Lemma lem7989669 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term19 A B f s x y) = (term21 A B f s x y).
Proof. exact (@lem7989668 ((f x) = (f y)) (@IN A y s) (term22 A s x y)). Qed.
Lemma lem7989674 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (y : A) : (term18 A B s f x y) = (term21 A B f s x y).
Proof. exact (TRANS (@lem7989666 A B f s x y) (@lem7989669 A B f s x y)). Qed.
Lemma lem7989683 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term23 A B s f x) = (term24 A B f s x).
Proof. exact (fun_ext (fun y : A => @lem7989674 A B f s x y)). Qed.
Lemma lem7989684 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7989685 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term25 A B s f x) = (term26 A B f s x).
Proof. exact (MK_COMB (@lem7989684 A) (@lem7989683 A B f s x)). Qed.
Lemma lem7989690 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term27 A B s f) = (term28 A B f s).
Proof. exact (fun_ext (fun x : A => @lem7989685 A B f s x)). Qed.
Lemma lem7989691 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7989692 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term16 A B s f) = (term29 A B f s).
Proof. exact (MK_COMB (@lem7989691 A) (@lem7989690 A B f s)). Qed.
Lemma lem7989697 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7989698 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term30 A B s f) = (term31 A B f s).
Proof. exact (MK_COMB (@lem7989697) (@lem7989692 A B f s)). Qed.
Lemma lem7989699 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term17 A B f s n) = (term17 A B f s n).
Proof. exact (eq_refl (term17 A B f s n)). Qed.
Lemma lem7989700 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term32 A B f s n) = (term33 A B f s n).
Proof. exact (MK_COMB (@lem7989698 A B f s) (@lem7989699 A B f s n)). Qed.
Lemma lem7989703 {A : Type'} (s : A -> Prop) (n : nat) : (term34 A s n) = (term34 A s n).
Proof. exact (eq_refl (term34 A s n)). Qed.
Lemma lem7989704 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term15 A B f s n) = (term35 A B f s n).
Proof. exact (MK_COMB (@lem7989703 A s n) (@lem7989700 A B f s n)). Qed.
Lemma lem7989707 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term14 A B f s n) = (term35 A B f s n).
Proof. exact (TRANS (@lem7989651 A B f s n) (@lem7989704 A B f s n)). Qed.
Lemma lem7989708 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term36 A B f s) = (term37 A B f s).
Proof. exact (fun_ext (fun n : nat => @lem7989707 A B f s n)). Qed.
Lemma lem7989709 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7989710 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term38 A B f s) = (term39 A B f s).
Proof. exact (MK_COMB (@lem7989709) (@lem7989708 A B f s)). Qed.
Lemma lem7989715 {A B : Type'} (f : A -> B) : (term40 A B f) = (term41 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7989710 A B f s)). Qed.
Lemma lem7989716 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7989717 {A B : Type'} (f : A -> B) : (term42 A B f) = (term43 A B f).
Proof. exact (MK_COMB (@lem7989716 A) (@lem7989715 A B f)). Qed.
Lemma lem7989722 {A B : Type'} : (term44 A B) = (term45 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem7989717 A B f)). Qed.
Lemma lem7989723 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem7989724 {A B : Type'} : (term46 A B) = (term47 A B).
Proof. exact (MK_COMB (@lem7989723 A B) (@lem7989722 A B)). Qed.
Lemma lem7989729 {A B : Type'} : term47 A B.
Proof. exact (EQ_MP (@lem7989724 A B) (@lem4004559 A B)). Qed.
Lemma lem7989730 {A B : Type'} (h1 : term47 A B) : term47 A B.
Proof. exact (h1). Qed.
Lemma lem7989731 {A B : Type'} (f : A -> B) (h1 : term47 A B) : term48 A B f.
Proof. exact (@lem7989730 A B h1 f). Qed.
Lemma lem7989732 {A B : Type'} (f : A -> B) : (term48 A B f) = (term43 A B f).
Proof. exact (eq_refl (term48 A B f)). Qed.
Lemma lem7989733 {A B : Type'} (f : A -> B) (h1 : term47 A B) : term43 A B f.
Proof. exact (EQ_MP (@lem7989732 A B f) (@lem7989731 A B f h1)). Qed.
Lemma lem7989734 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term47 A B) : term49 A B f s.
Proof. exact (@lem7989733 A B f h1 s). Qed.
Lemma lem7989735 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term49 A B f s) = (term39 A B f s).
Proof. exact (eq_refl (term49 A B f s)). Qed.
Lemma lem7989736 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term47 A B) : term39 A B f s.
Proof. exact (EQ_MP (@lem7989735 A B f s) (@lem7989734 A B f s h1)). Qed.
Lemma lem7989737 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term47 A B) : term50 A B f s n.
Proof. exact (@lem7989736 A B f s h1 n). Qed.
Lemma lem7989738 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term50 A B f s n) = (term35 A B f s n).
Proof. exact (eq_refl (term50 A B f s n)). Qed.
Lemma lem7989739 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term47 A B) : term35 A B f s n.
Proof. exact (EQ_MP (@lem7989738 A B f s n) (@lem7989737 A B f s n h1)). Qed.
Lemma lem7989740 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : @HAS_SIZE A s n.
Proof. exact (h1). Qed.
Lemma lem7989741 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term47 A B) (h2 : @HAS_SIZE A s n) : term33 A B f s n.
Proof. exact (@lem7989739 A B f s n h1 (@lem7989740 A s n h2)). Qed.
Lemma lem7989742 {A B : Type'} (s : A -> Prop) (n : nat) (h1 : term47 A B) (h2 : @HAS_SIZE A s n) : term51 A B s n.
Proof. exact (fun f : A -> B => @lem7989741 A B f s n h1 h2). Qed.
Lemma lem7989743 {A B : Type'} (s : A -> Prop) (n : nat) (h1 : term47 A B) : term52 A B s n.
Proof. exact (fun h0 : @HAS_SIZE A s n => @lem7989742 A B s n h1 h0). Qed.
Lemma lem7989744 {A B : Type'} (s : A -> Prop) (h1 : term47 A B) : term53 A B s.
Proof. exact (fun n : nat => @lem7989743 A B s n h1). Qed.
Lemma lem7989745 {A B : Type'} (h1 : term47 A B) : term54 A B.
Proof. exact (fun s : A -> Prop => @lem7989744 A B s h1). Qed.
Lemma lem7989746 {A B : Type'} : term55 A B.
Proof. exact (fun h0 : term47 A B => @lem7989745 A B h0). Qed.
Lemma lem7989747 {A B : Type'} : term54 A B.
Proof. exact (@lem7989746 A B (@lem7989729 A B)). Qed.
Lemma lem7989748 {A B : Type'} (s : A -> Prop) : term56 A B s.
Proof. exact (@lem7989747 A B s). Qed.
Lemma lem7989749 {A B : Type'} (s : A -> Prop) : (term56 A B s) = (term53 A B s).
Proof. exact (eq_refl (term56 A B s)). Qed.
Lemma lem7989750 {A B : Type'} (s : A -> Prop) : term53 A B s.
Proof. exact (EQ_MP (@lem7989749 A B s) (@lem7989748 A B s)). Qed.
Lemma lem7989751 {A B : Type'} (s : A -> Prop) (n : nat) : term57 A B s n.
Proof. exact (@lem7989750 A B s n). Qed.
Lemma lem7989752 {A B : Type'} (s : A -> Prop) (n : nat) : (term57 A B s n) = (term52 A B s n).
Proof. exact (eq_refl (term57 A B s n)). Qed.
Lemma lem7989754 {A : Type'} (m : nat) (h1 : @HAS_SIZE A (@UNIV A) m) : @HAS_SIZE A (@UNIV A) m.
Proof. exact (h1). Qed.
Lemma lem7989755 {A N : Type'} (m : nat) (h1 : term58 A N m) : term58 A N m.
Proof. exact (h1). Qed.
Lemma lem7989756 {A : Type'} (s : A -> Prop) : term59 A s.
Proof. exact (@lem7605765 A s). Qed.
Lemma lem7989757 {A : Type'} (s : A -> Prop) : (term59 A s) = (term60 A s).
Proof. exact (eq_refl (term59 A s)). Qed.
Lemma lem7989758 {A : Type'} (s : A -> Prop) : term60 A s.
Proof. exact (EQ_MP (@lem7989757 A s) (@lem7989756 A s)). Qed.
Lemma lem7989759 {A : Type'} (s : A -> Prop) : (term60 A s) = ((term60 A s) = True).
Proof. exact (@lem7 (term60 A s)). Qed.
Lemma lem7989761 {A B : Type'} (m : nat) : term61 A B m.
Proof. exact (@lem4582295 A B m). Qed.
Lemma lem7989762 {A B : Type'} (m : nat) : (term61 A B m) = (term62 A B m).
Proof. exact (eq_refl (term61 A B m)). Qed.
Lemma lem7989763 {A B : Type'} (m : nat) : term62 A B m.
Proof. exact (EQ_MP (@lem7989762 A B m) (@lem7989761 A B m)). Qed.
Lemma lem7989764 {A B : Type'} (m : nat) (n : nat) : term63 A B m n.
Proof. exact (@lem7989763 A B m n). Qed.
Lemma lem7989765 {A B : Type'} (n : nat) (m : nat) : (term63 A B m n) = (term64 A B n m).
Proof. exact (eq_refl (term63 A B m n)). Qed.
Lemma lem7989766 {A B : Type'} (n : nat) (m : nat) : term64 A B n m.
Proof. exact (EQ_MP (@lem7989765 A B n m) (@lem7989764 A B m n)). Qed.
Lemma lem7989767 {A B : Type'} (m : nat) (n : nat) (h1 : term65 A B m n) : term65 A B m n.
Proof. exact (h1). Qed.
Lemma lem7989768 {A B : Type'} (m : nat) (n : nat) (h1 : term65 A B m n) : term66 A B n m.
Proof. exact (@lem7989766 A B n m (@lem7989767 A B m n h1)). Qed.
Lemma lem7989769 {A B : Type'} (n : nat) (m : nat) : (term66 A B n m) = ((term66 A B n m) = True).
Proof. exact (@lem7 (term66 A B n m)). Qed.
Lemma lem7989770 {A B : Type'} (m : nat) (n : nat) (h1 : term65 A B m n) : (term66 A B n m) = True.
Proof. exact (EQ_MP (@lem7989769 A B n m) (@lem7989768 A B m n h1)). Qed.
Lemma lem7989776 {A : Type'} (m : nat) : (@HAS_SIZE A (@UNIV A) m) = ((@HAS_SIZE A (@UNIV A) m) = True).
Proof. exact (@lem7 (@HAS_SIZE A (@UNIV A) m)). Qed.
Lemma lem7989779 {A B : Type'} (n : nat) (m : nat) : term67 A B n m.
Proof. exact (fun h0 : term65 A B m n => @lem7989770 A B m n h0). Qed.
Lemma lem7989780 {A N : Type'} (n : nat) (m : nat) : term68 A N n m.
Proof. exact (@lem7989779 (finite_image N) A n m). Qed.
Lemma lem7989781 {A N : Type'} (m : nat) : term69 A N m.
Proof. exact (@lem7989780 A N m (@dimindex N (@UNIV N))). Qed.
Lemma lem7989785 {A : Type'} (s : A -> Prop) : (term60 A s) = True.
Proof. exact (EQ_MP (@lem7989759 A s) (@lem7989758 A s)). Qed.
Lemma lem7989786 {N : Type'} (s : N -> Prop) : (term60 N s) = True.
Proof. exact (@lem7989785 N s). Qed.
Lemma lem7989787 {N : Type'} : (term70 N) = True.
Proof. exact (@lem7989786 N (@UNIV N)). Qed.
Lemma lem7989788 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7989789 {N : Type'} : (term71 N) = (and True).
Proof. exact (MK_COMB (@lem7989788) (@lem7989787 N)). Qed.
Lemma lem7989791 {A : Type'} (m : nat) (h1 : @HAS_SIZE A (@UNIV A) m) : (@HAS_SIZE A (@UNIV A) m) = True.
Proof. exact (EQ_MP (@lem7989776 A m) (@lem7989754 A m h1)). Qed.
Lemma lem7989792 {A N : Type'} (m : nat) (h1 : @HAS_SIZE A (@UNIV A) m) : (term72 A N m) = (True /\ True).
Proof. exact (MK_COMB (@lem7989789 N) (@lem7989791 A m h1)). Qed.
Lemma lem7989794 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7989795 : (True /\ True) = True.
Proof. exact (@lem7989794 True). Qed.
Lemma lem7989796 {A N : Type'} (m : nat) (h1 : @HAS_SIZE A (@UNIV A) m) : (term72 A N m) = True.
Proof. exact (TRANS (@lem7989792 A N m h1) (@lem7989795)). Qed.
Lemma lem7989797 {A N : Type'} (m : nat) (h1 : @HAS_SIZE A (@UNIV A) m) : True = (term72 A N m).
Proof. exact (SYM (@lem7989796 A N m h1)). Qed.
Lemma lem7989798 {A N : Type'} (m : nat) (h1 : @HAS_SIZE A (@UNIV A) m) : term72 A N m.
Proof. exact (EQ_MP (@lem7989797 A N m h1) (@lem0)). Qed.
Lemma lem7989799 {A N : Type'} (m : nat) (h1 : @HAS_SIZE A (@UNIV A) m) : (term58 A N m) = True.
Proof. exact (@lem7989781 A N m (@lem7989798 A N m h1)). Qed.
Lemma lem7989800 {A N : Type'} (m : nat) (h1 : @HAS_SIZE A (@UNIV A) m) : True = (term58 A N m).
Proof. exact (SYM (@lem7989799 A N m h1)). Qed.
Lemma lem7989801 {A N : Type'} (m : nat) (h1 : @HAS_SIZE A (@UNIV A) m) : term58 A N m.
Proof. exact (EQ_MP (@lem7989800 A N m h1) (@lem0)). Qed.
Lemma lem7989802 {A N : Type'} (m : nat) (h1 : term58 A N m) : term58 A N m.
Proof. exact (h1). Qed.
Lemma lem7989804 {A B : Type'} (s : A -> Prop) (n : nat) : term52 A B s n.
Proof. exact (EQ_MP (@lem7989752 A B s n) (@lem7989751 A B s n)). Qed.
Lemma lem7989805 {A B N : Type'} (s : type62 A N) (n : nat) : term73 A B N s n.
Proof. exact (@lem7989804 (type35 A N) B s n). Qed.
Lemma lem7989806 {A B N : Type'} (m : nat) : term74 A B N m.
Proof. exact (@lem7989805 A B N (@UNIV ((finite_image N) -> A)) (term75 N m)). Qed.
Lemma lem7989807 {A B N : Type'} (m : nat) (h1 : term58 A N m) : term76 A B N m.
Proof. exact (@lem7989806 A B N m (@lem7989802 A N m h1)). Qed.
Lemma lem7989808 {A N : Type'} (m : nat) (h1 : term58 A N m) : term77 A N m.
Proof. exact (@lem7989807 A (cart A N) N m h1). Qed.
Lemma lem7989809 {A N : Type'} (m : nat) (h1 : term58 A N m) : term78 A N m.
Proof. exact (@lem7989808 A N m h1 (@mk_cart A N)). Qed.
Lemma lem7989810 {A N : Type'} (m : nat) : (term78 A N m) = (term79 A N m).
Proof. exact (eq_refl (term78 A N m)). Qed.
Lemma lem7989811 {A N : Type'} (m : nat) (h1 : term58 A N m) : term79 A N m.
Proof. exact (EQ_MP (@lem7989810 A N m) (@lem7989809 A N m h1)). Qed.
Lemma lem7989833 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem7989635 A x) (@lem7989634 A x)). Qed.
Lemma lem7989834 {A N : Type'} (x : type35 A N) : (@IN ((finite_image N) -> A) x (@UNIV ((finite_image N) -> A))) = True.
Proof. exact (@lem7989833 (type35 A N) x). Qed.
Lemma lem7989835 {A N : Type'} (y : type35 A N) : (@IN ((finite_image N) -> A) y (@UNIV ((finite_image N) -> A))) = True.
Proof. exact (@lem7989834 A N y). Qed.
Lemma lem7989836 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7989837 {A N : Type'} (y : type35 A N) : (term80 A N y) = (imp True).
Proof. exact (MK_COMB (@lem7989836) (@lem7989835 A N y)). Qed.
Lemma lem7989841 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem7989635 A x) (@lem7989634 A x)). Qed.
Lemma lem7989842 {A N : Type'} (x : type35 A N) : (@IN ((finite_image N) -> A) x (@UNIV ((finite_image N) -> A))) = True.
Proof. exact (@lem7989841 (type35 A N) x). Qed.
Lemma lem7989843 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7989844 {A N : Type'} (x : type35 A N) : (term80 A N x) = (imp True).
Proof. exact (MK_COMB (@lem7989843) (@lem7989842 A N x)). Qed.
Lemma lem7989847 {A N : Type'} (x : type35 A N) (y : type35 A N) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem7989848 {A N : Type'} (x : type35 A N) (y : type35 A N) : (term81 A N x y) = (term82 A N x y).
Proof. exact (MK_COMB (@lem7989844 A N x) (@lem7989847 A N x y)). Qed.
Lemma lem7989850 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem7989851 {A N : Type'} (x : type35 A N) (y : type35 A N) : (term82 A N x y) = (x = y).
Proof. exact (@lem7989850 (x = y)). Qed.
Lemma lem7989854 {A N : Type'} (x : type35 A N) (y : type35 A N) : (term81 A N x y) = (x = y).
Proof. exact (TRANS (@lem7989848 A N x y) (@lem7989851 A N x y)). Qed.
Lemma lem7989855 {A N : Type'} (x : type35 A N) (y : type35 A N) : (term83 A N x y) = (term82 A N x y).
Proof. exact (MK_COMB (@lem7989837 A N y) (@lem7989854 A N x y)). Qed.
Lemma lem7989857 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem7989858 {A N : Type'} (x : type35 A N) (y : type35 A N) : (term82 A N x y) = (x = y).
Proof. exact (@lem7989857 (x = y)). Qed.
Lemma lem7989861 {A N : Type'} (x : type35 A N) (y : type35 A N) : (term83 A N x y) = (x = y).
Proof. exact (TRANS (@lem7989855 A N x y) (@lem7989858 A N x y)). Qed.
Lemma lem7989862 {A N : Type'} (x : type35 A N) (y : type35 A N) : (term84 A N x y) = (term84 A N x y).
Proof. exact (eq_refl (term84 A N x y)). Qed.
Lemma lem7989863 {A N : Type'} (x : type35 A N) (y : type35 A N) : (term85 A N x y) = (term86 A N x y).
Proof. exact (MK_COMB (@lem7989862 A N x y) (@lem7989861 A N x y)). Qed.
Lemma lem7989868 {A N : Type'} (x : type35 A N) : (term87 A N x) = (term88 A N x).
Proof. exact (fun_ext (fun y : type35 A N => @lem7989863 A N x y)). Qed.
Lemma lem7989869 {A N : Type'} : (@all ((finite_image N) -> A)) = (@all ((finite_image N) -> A)).
Proof. exact (eq_refl (@all ((finite_image N) -> A))). Qed.
Lemma lem7989870 {A N : Type'} (x : type35 A N) : (term89 A N x) = (term90 A N x).
Proof. exact (MK_COMB (@lem7989869 A N) (@lem7989868 A N x)). Qed.
Lemma lem7989875 {A N : Type'} : (term91 A N) = (term92 A N).
Proof. exact (fun_ext (fun x : type35 A N => @lem7989870 A N x)). Qed.
Lemma lem7989876 {A N : Type'} : (@all ((finite_image N) -> A)) = (@all ((finite_image N) -> A)).
Proof. exact (eq_refl (@all ((finite_image N) -> A))). Qed.
Lemma lem7989877 {A N : Type'} : (term93 A N) = (term94 A N).
Proof. exact (MK_COMB (@lem7989876 A N) (@lem7989875 A N)). Qed.
Lemma lem7989882 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7989883 {A N : Type'} : (term95 A N) = (term96 A N).
Proof. exact (MK_COMB (@lem7989882) (@lem7989877 A N)). Qed.
Lemma lem7989884 {A N : Type'} (m : nat) : (term97 A N m) = (term97 A N m).
Proof. exact (eq_refl (term97 A N m)). Qed.
Lemma lem7989885 {A N : Type'} (m : nat) : (term79 A N m) = (term98 A N m).
Proof. exact (MK_COMB (@lem7989883 A N) (@lem7989884 A N m)). Qed.
Lemma lem7989888 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7989889 {A N : Type'} (m : nat) : (term99 A N m) = (term100 A N m).
Proof. exact (MK_COMB (@lem7989888) (@lem7989885 A N m)). Qed.
Lemma lem7989890 {A N : Type'} (m : nat) : (term101 A N m) = (term101 A N m).
Proof. exact (eq_refl (term101 A N m)). Qed.
Lemma lem7989891 {A N : Type'} (m : nat) : (term102 A N m) = (term103 A N m).
Proof. exact (MK_COMB (@lem7989889 A N m) (@lem7989890 A N m)). Qed.
Lemma lem7989894 {A N : Type'} (m : nat) : (term103 A N m) = (term102 A N m).
Proof. exact (SYM (@lem7989891 A N m)). Qed.
Lemma lem7989896 (p : Prop) (q : Prop) (r : Prop) : term104 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem7989897 {A N : Type'} (m : nat) : term105 A N m.
Proof. exact (@lem7989896 (term94 A N) (term97 A N m) (term101 A N m)). Qed.
Lemma lem7989899 (p : Prop) : p = (term106 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7989900 {A N : Type'} : (term94 A N) = (term107 A N).
Proof. exact (@lem7989899 (term94 A N)). Qed.
Lemma lem7989901 {A N : Type'} : (term107 A N) = (term94 A N).
Proof. exact (SYM (@lem7989900 A N)). Qed.
Lemma lem7989902 {A N : Type'} (h1 : term108 A N) : term108 A N.
Proof. exact (h1). Qed.
Lemma lem7989903 {A N : Type'} : term109 A N.
Proof. exact (@lem7614851 A N). Qed.
Lemma lem7989908 {A N : Type'} (h1 : term110 A N) : term110 A N.
Proof. exact (h1). Qed.
Lemma lem7989909 {A N : Type'} : term111 A N.
Proof. exact (fun h0 : term110 A N => @lem7989908 A N h0). Qed.
Lemma lem7989910 {A N : Type'} (h1 : term111 A N) : term111 A N.
Proof. exact (h1). Qed.
Lemma lem7989911 {A N : Type'} (h1 : term110 A N) : term110 A N.
Proof. exact (h1). Qed.
Lemma lem7989912 {A N : Type'} (h1 : term110 A N) (h2 : term111 A N) : term110 A N.
Proof. exact (@lem7989910 A N h2 (@lem7989911 A N h1)). Qed.
Lemma lem7989913 {A N : Type'} (h1 : term110 A N) : term112 A N.
Proof. exact (fun h0 : term111 A N => @lem7989912 A N h1 h0). Qed.
Lemma lem7989914 {A N : Type'} (h1 : term111 A N) : term111 A N.
Proof. exact (h1). Qed.
Lemma lem7989915 {A N : Type'} (h1 : term110 A N) (h2 : term111 A N) : term110 A N.
Proof. exact (@lem7989913 A N h1 (@lem7989914 A N h2)). Qed.
Lemma lem7989916 {A N : Type'} (h1 : term111 A N) : term111 A N.
Proof. exact (fun h0 : term110 A N => @lem7989915 A N h0 h1). Qed.
Lemma lem7989917 {A N : Type'} : term113 A N.
Proof. exact (fun h0 : term111 A N => @lem7989916 A N h0). Qed.
Lemma lem7989920 {A N : Type'} : term111 A N.
Proof. exact (@lem7989917 A N (@lem7989909 A N)). Qed.
Lemma lem7989921 {A N : Type'} : term111 A N.
Proof. exact (@lem7989920 A N). Qed.
Lemma lem7989935 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7989936 {A N : Type'} : (term114 A N) = (term115 A N).
Proof. exact (@lem7989935 (term109 A N)). Qed.
Lemma lem7989948 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem16462 t)). Qed.
Lemma lem7989949 {A N : Type'} (r : type35 A N) : (True = ((term116 A N r) = r)) = ((term116 A N r) = r).
Proof. exact (@lem7989948 ((term116 A N r) = r)). Qed.
Lemma lem7989950 {A N : Type'} : (term117 A N) = (term118 A N).
Proof. exact (fun_ext (fun r : type35 A N => @lem7989949 A N r)). Qed.
Lemma lem7989951 {A N : Type'} : (@all ((finite_image N) -> A)) = (@all ((finite_image N) -> A)).
Proof. exact (eq_refl (@all ((finite_image N) -> A))). Qed.
Lemma lem7989952 {A N : Type'} : (term119 A N) = (term120 A N).
Proof. exact (MK_COMB (@lem7989951 A N) (@lem7989950 A N)). Qed.
Lemma lem7989957 {A N : Type'} : (term121 A N) = (term121 A N).
Proof. exact (eq_refl (term121 A N)). Qed.
Lemma lem7989958 {A N : Type'} : (term109 A N) = (term122 A N).
Proof. exact (MK_COMB (@lem7989957 A N) (@lem7989952 A N)). Qed.
Lemma lem7989961 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7989962 {A N : Type'} : (term115 A N) = (term123 A N).
Proof. exact (MK_COMB (@lem7989961) (@lem7989958 A N)). Qed.
Lemma lem7989963 {A N : Type'} : (term114 A N) = (term123 A N).
Proof. exact (TRANS (@lem7989936 A N) (@lem7989962 A N)). Qed.
Lemma lem7989964 {A N : Type'} : (term124 A N) = (term124 A N).
Proof. exact (eq_refl (term124 A N)). Qed.
Lemma lem7989971 {A N : Type'} : (term110 A N) = (term125 A N).
Proof. exact (MK_COMB (@lem7989964 A N) (@lem7989963 A N)). Qed.
Lemma lem7989972 {A N : Type'} (r : type35 A N) : ((term116 A N r) = r) = ((term116 A N r) = r).
Proof. exact (eq_refl ((term116 A N r) = r)). Qed.
Lemma lem7989973 {A N : Type'} : (term118 A N) = (term118 A N).
Proof. exact (fun_ext (fun r : type35 A N => @lem7989972 A N r)). Qed.
Lemma lem7989974 {A N : Type'} : (@all ((finite_image N) -> A)) = (@all ((finite_image N) -> A)).
Proof. exact (eq_refl (@all ((finite_image N) -> A))). Qed.
Lemma lem7989975 {A N : Type'} : (term120 A N) = (term120 A N).
Proof. exact (MK_COMB (@lem7989974 A N) (@lem7989973 A N)). Qed.
Lemma lem7989976 {A N : Type'} (a : cart A N) : ((term126 A N a) = a) = ((term126 A N a) = a).
Proof. exact (eq_refl ((term126 A N a) = a)). Qed.
Lemma lem7989977 {A N : Type'} : (term127 A N) = (term127 A N).
Proof. exact (fun_ext (fun a : cart A N => @lem7989976 A N a)). Qed.
Lemma lem7989978 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem7989979 {A N : Type'} : (term128 A N) = (term128 A N).
Proof. exact (MK_COMB (@lem7989978 A N) (@lem7989977 A N)). Qed.
Lemma lem7989980 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7989981 {A N : Type'} : (term121 A N) = (term121 A N).
Proof. exact (MK_COMB (@lem7989980) (@lem7989979 A N)). Qed.
Lemma lem7989982 {A N : Type'} : (term122 A N) = (term122 A N).
Proof. exact (MK_COMB (@lem7989981 A N) (@lem7989975 A N)). Qed.
Lemma lem7989983 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7989984 {A N : Type'} : (term123 A N) = (term123 A N).
Proof. exact (MK_COMB (@lem7989983) (@lem7989982 A N)). Qed.
Lemma lem7989989 {A N : Type'} (x : type35 A N) (y : type35 A N) : (term86 A N x y) = (term86 A N x y).
Proof. exact (eq_refl (term86 A N x y)). Qed.
Lemma lem7989990 {A N : Type'} (x : type35 A N) : (term88 A N x) = (term88 A N x).
Proof. exact (fun_ext (fun y : type35 A N => @lem7989989 A N x y)). Qed.
Lemma lem7989991 {A N : Type'} : (@all ((finite_image N) -> A)) = (@all ((finite_image N) -> A)).
Proof. exact (eq_refl (@all ((finite_image N) -> A))). Qed.
Lemma lem7989992 {A N : Type'} (x : type35 A N) : (term90 A N x) = (term90 A N x).
Proof. exact (MK_COMB (@lem7989991 A N) (@lem7989990 A N x)). Qed.
Lemma lem7989993 {A N : Type'} : (term92 A N) = (term92 A N).
Proof. exact (fun_ext (fun x : type35 A N => @lem7989992 A N x)). Qed.
Lemma lem7989994 {A N : Type'} : (@all ((finite_image N) -> A)) = (@all ((finite_image N) -> A)).
Proof. exact (eq_refl (@all ((finite_image N) -> A))). Qed.
Lemma lem7989995 {A N : Type'} : (term94 A N) = (term94 A N).
Proof. exact (MK_COMB (@lem7989994 A N) (@lem7989993 A N)). Qed.
Lemma lem7989996 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7989997 {A N : Type'} : (term108 A N) = (term108 A N).
Proof. exact (MK_COMB (@lem7989996) (@lem7989995 A N)). Qed.
Lemma lem7989998 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7989999 {A N : Type'} : (term124 A N) = (term124 A N).
Proof. exact (MK_COMB (@lem7989998) (@lem7989997 A N)). Qed.
Lemma lem7990000 {A N : Type'} : (term125 A N) = (term125 A N).
Proof. exact (MK_COMB (@lem7989999 A N) (@lem7989984 A N)). Qed.
Lemma lem7990033 {A N : Type'} : (term110 A N) = (term125 A N).
Proof. exact (TRANS (@lem7989971 A N) (@lem7990000 A N)). Qed.
Lemma lem7990034 {A N : Type'} : (term125 A N) = (term110 A N).
Proof. exact (SYM (@lem7990033 A N)). Qed.
Lemma lem7990035 {A N : Type'} (h1 : term108 A N) : term108 A N.
Proof. exact (h1). Qed.
Lemma lem7990036 {A N : Type'} (h1 : term122 A N) : term122 A N.
Proof. exact (h1). Qed.
Lemma lem7990043 {A N : Type'} (x : type35 A N) (y : type35 A N) : (term129 A N x y) = (term130 A N x y).
Proof. exact (@lem17362 ((@mk_cart A N x) = (@mk_cart A N y)) (x = y)). Qed.
Lemma lem7990044 {A N : Type'} (P : type62 A N) : (term131 A N P) = (term132 A N P).
Proof. exact (@lem18392 (type35 A N) P). Qed.
Lemma lem7990045 {A N : Type'} (x : type35 A N) : (term133 A N x) = (term134 A N x).
Proof. exact (@lem7990044 A N (term88 A N x)). Qed.
Lemma lem7990046 {A N : Type'} (x : type35 A N) (y : type35 A N) : (term135 A N x y) = (term86 A N x y).
Proof. exact (eq_refl (term135 A N x y)). Qed.
Lemma lem7990047 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7990048 {A N : Type'} (x : type35 A N) (y : type35 A N) : (term136 A N x y) = (term129 A N x y).
Proof. exact (MK_COMB (@lem7990047) (@lem7990046 A N x y)). Qed.
Lemma lem7990049 {A N : Type'} (x : type35 A N) (y : type35 A N) : (term136 A N x y) = (term130 A N x y).
Proof. exact (TRANS (@lem7990048 A N x y) (@lem7990043 A N x y)). Qed.
Lemma lem7990050 {A N : Type'} (x : type35 A N) : (term137 A N x) = (term138 A N x).
Proof. exact (fun_ext (fun y : type35 A N => @lem7990049 A N x y)). Qed.
Lemma lem7990051 {A N : Type'} : (@ex ((finite_image N) -> A)) = (@ex ((finite_image N) -> A)).
Proof. exact (eq_refl (@ex ((finite_image N) -> A))). Qed.
Lemma lem7990052 {A N : Type'} (x : type35 A N) : (term134 A N x) = (term139 A N x).
Proof. exact (MK_COMB (@lem7990051 A N) (@lem7990050 A N x)). Qed.
Lemma lem7990053 {A N : Type'} (x : type35 A N) : (term133 A N x) = (term139 A N x).
Proof. exact (TRANS (@lem7990045 A N x) (@lem7990052 A N x)). Qed.
Lemma lem7990054 {A N : Type'} (P : type62 A N) : (term131 A N P) = (term132 A N P).
Proof. exact (@lem18392 (type35 A N) P). Qed.
Lemma lem7990055 {A N : Type'} : (term108 A N) = (term140 A N).
Proof. exact (@lem7990054 A N (term92 A N)). Qed.
Lemma lem7990056 {A N : Type'} (x : type35 A N) : (term141 A N x) = (term90 A N x).
Proof. exact (eq_refl (term141 A N x)). Qed.
Lemma lem7990057 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7990058 {A N : Type'} (x : type35 A N) : (term142 A N x) = (term133 A N x).
Proof. exact (MK_COMB (@lem7990057) (@lem7990056 A N x)). Qed.
Lemma lem7990059 {A N : Type'} (x : type35 A N) : (term142 A N x) = (term139 A N x).
Proof. exact (TRANS (@lem7990058 A N x) (@lem7990053 A N x)). Qed.
Lemma lem7990060 {A N : Type'} : (term143 A N) = (term144 A N).
Proof. exact (fun_ext (fun x : type35 A N => @lem7990059 A N x)). Qed.
Lemma lem7990061 {A N : Type'} : (@ex ((finite_image N) -> A)) = (@ex ((finite_image N) -> A)).
Proof. exact (eq_refl (@ex ((finite_image N) -> A))). Qed.
Lemma lem7990062 {A N : Type'} : (term140 A N) = (term145 A N).
Proof. exact (MK_COMB (@lem7990061 A N) (@lem7990060 A N)). Qed.
Lemma lem7990119 {A N : Type'} : (term108 A N) = (term145 A N).
Proof. exact (TRANS (@lem7990055 A N) (@lem7990062 A N)). Qed.
Lemma lem7990120 {A N : Type'} (h1 : term108 A N) : term145 A N.
Proof. exact (EQ_MP (@lem7990119 A N) (@lem7990035 A N h1)). Qed.
Lemma lem7990121 {A N : Type'} (a : cart A N) : ((term126 A N a) = a) = ((term126 A N a) = a).
Proof. exact (eq_refl ((term126 A N a) = a)). Qed.
Lemma lem7990122 {A N : Type'} : (term127 A N) = (term127 A N).
Proof. exact (fun_ext (fun a : cart A N => @lem7990121 A N a)). Qed.
Lemma lem7990123 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem7990124 {A N : Type'} : (term128 A N) = (term128 A N).
Proof. exact (MK_COMB (@lem7990123 A N) (@lem7990122 A N)). Qed.
Lemma lem7990125 {A N : Type'} (r : type35 A N) : ((term116 A N r) = r) = ((term116 A N r) = r).
Proof. exact (eq_refl ((term116 A N r) = r)). Qed.
Lemma lem7990126 {A N : Type'} : (term118 A N) = (term118 A N).
Proof. exact (fun_ext (fun r : type35 A N => @lem7990125 A N r)). Qed.
Lemma lem7990127 {A N : Type'} : (@all ((finite_image N) -> A)) = (@all ((finite_image N) -> A)).
Proof. exact (eq_refl (@all ((finite_image N) -> A))). Qed.
Lemma lem7990128 {A N : Type'} : (term120 A N) = (term120 A N).
Proof. exact (MK_COMB (@lem7990127 A N) (@lem7990126 A N)). Qed.
Lemma lem7990129 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7990130 {A N : Type'} : (term121 A N) = (term121 A N).
Proof. exact (MK_COMB (@lem7990129) (@lem7990124 A N)). Qed.
Lemma lem7990143 {A N : Type'} : (term122 A N) = (term122 A N).
Proof. exact (MK_COMB (@lem7990130 A N) (@lem7990128 A N)). Qed.
Lemma lem7990144 {A N : Type'} (h1 : term122 A N) : term122 A N.
Proof. exact (EQ_MP (@lem7990143 A N) (@lem7990036 A N h1)). Qed.
Lemma lem7990145 {A N : Type'} (x : type35 A N) (h1 : term139 A N x) : term139 A N x.
Proof. exact (h1). Qed.
Lemma lem7990155 {A N : Type'} (r : type35 A N) : ((term116 A N r) = r) = ((term116 A N r) = r).
Proof. exact (eq_refl ((term116 A N r) = r)). Qed.
Lemma lem7990156 {A N : Type'} : (term118 A N) = (term118 A N).
Proof. exact (fun_ext (fun r : type35 A N => @lem7990155 A N r)). Qed.
Lemma lem7990157 {A N : Type'} : (@all ((finite_image N) -> A)) = (@all ((finite_image N) -> A)).
Proof. exact (eq_refl (@all ((finite_image N) -> A))). Qed.
Lemma lem7990158 {A N : Type'} : (term120 A N) = (term120 A N).
Proof. exact (MK_COMB (@lem7990157 A N) (@lem7990156 A N)). Qed.
Lemma lem7990167 {A N : Type'} (a : cart A N) : ((term126 A N a) = a) = ((term126 A N a) = a).
Proof. exact (eq_refl ((term126 A N a) = a)). Qed.
Lemma lem7990168 {A N : Type'} : (term127 A N) = (term127 A N).
Proof. exact (fun_ext (fun a : cart A N => @lem7990167 A N a)). Qed.
Lemma lem7990169 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem7990170 {A N : Type'} : (term128 A N) = (term128 A N).
Proof. exact (MK_COMB (@lem7990169 A N) (@lem7990168 A N)). Qed.
Lemma lem7990171 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7990172 {A N : Type'} : (term121 A N) = (term121 A N).
Proof. exact (MK_COMB (@lem7990171) (@lem7990170 A N)). Qed.
Lemma lem7990173 {A N : Type'} : (term122 A N) = (term122 A N).
Proof. exact (MK_COMB (@lem7990172 A N) (@lem7990158 A N)). Qed.
Lemma lem7990174 {A N : Type'} (h1 : term122 A N) : term122 A N.
Proof. exact (EQ_MP (@lem7990173 A N) (@lem7990144 A N h1)). Qed.
Lemma lem7990194 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term130 A N x y) : term130 A N x y.
Proof. exact (h1). Qed.
Lemma lem7990197 {A N : Type'} (h1 : term122 A N) : term120 A N.
Proof. exact (proj2 (@lem7990174 A N h1)). Qed.
Lemma lem7990215 {A N : Type'} (r : type35 A N) : ((term116 A N r) = r) = ((term116 A N r) = r).
Proof. exact (eq_refl ((term116 A N r) = r)). Qed.
Lemma lem7990216 {A N : Type'} : (term118 A N) = (term118 A N).
Proof. exact (fun_ext (fun r : type35 A N => @lem7990215 A N r)). Qed.
Lemma lem7990217 {A N : Type'} : (@all ((finite_image N) -> A)) = (@all ((finite_image N) -> A)).
Proof. exact (eq_refl (@all ((finite_image N) -> A))). Qed.
Lemma lem7990219 {A N : Type'} : (term120 A N) = (term120 A N).
Proof. exact (MK_COMB (@lem7990217 A N) (@lem7990216 A N)). Qed.
Lemma lem7990220 {A N : Type'} (h1 : term122 A N) : term120 A N.
Proof. exact (EQ_MP (@lem7990219 A N) (@lem7990197 A N h1)). Qed.
Lemma lem7990224 {A N : Type'} (_105395 : type35 A N) (h1 : term122 A N) : term146 A N _105395.
Proof. exact (@lem7990220 A N h1 _105395). Qed.
Lemma lem7990225 {A N : Type'} (_105395 : type35 A N) : (term146 A N _105395) = ((term116 A N _105395) = _105395).
Proof. exact (eq_refl (term146 A N _105395)). Qed.
Lemma lem7990230 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term130 A N x y) : term147 A N x y.
Proof. exact (proj2 (@lem7990194 A N x y h1)). Qed.
Lemma lem7990235 {A N : Type'} : (@dest_cart A N) = (@dest_cart A N).
Proof. exact (eq_refl (@dest_cart A N)). Qed.
Lemma lem7990236 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) (h1 : _105396 = _105397) : _105396 = _105397.
Proof. exact (h1). Qed.
Lemma lem7990237 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) (h1 : _105396 = _105397) : (@dest_cart A N _105396) = (@dest_cart A N _105397).
Proof. exact (MK_COMB (@lem7990235 A N) (@lem7990236 A N _105396 _105397 h1)). Qed.
Lemma lem7990238 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) : term148 A N _105396 _105397.
Proof. exact (fun h0 : _105396 = _105397 => @lem7990237 A N _105396 _105397 h0). Qed.
Lemma lem7990240 (a : Prop) (b : Prop) : (a -> b) = (term149 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7990241 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) : (term148 A N _105396 _105397) = (term150 A N _105396 _105397).
Proof. exact (@lem7990240 (_105396 = _105397) ((@dest_cart A N _105396) = (@dest_cart A N _105397))). Qed.
Lemma lem7990242 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) : term150 A N _105396 _105397.
Proof. exact (EQ_MP (@lem7990241 A N _105396 _105397) (@lem7990238 A N _105396 _105397)). Qed.
Lemma lem7990254 {A N : Type'} (x : type35 A N) (y : type35 A N) (z : type35 A N) : term151 A N x y z.
Proof. exact (@lem21385 (type35 A N) x y z). Qed.
Lemma lem7990256 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term130 A N x y) : (@mk_cart A N x) = (@mk_cart A N y).
Proof. exact (proj1 (@lem7990194 A N x y h1)). Qed.
Lemma lem7990257 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term130 A N x y) : term152 A N x y.
Proof. exact (fun h0 : term153 A N x y => @lem7990256 A N x y h1). Qed.
Lemma lem7990259 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7990260 {A N : Type'} (x : type35 A N) (y : type35 A N) : (term152 A N x y) = ((@mk_cart A N x) = (@mk_cart A N y)).
Proof. exact (@lem7990259 ((@mk_cart A N x) = (@mk_cart A N y))). Qed.
Lemma lem7990261 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term130 A N x y) : (@mk_cart A N x) = (@mk_cart A N y).
Proof. exact (EQ_MP (@lem7990260 A N x y) (@lem7990257 A N x y h1)). Qed.
Lemma lem7990267 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7990268 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) : (term150 A N _105396 _105397) = (term155 A N _105396 _105397).
Proof. exact (@lem7990267 ((@dest_cart A N _105396) = (@dest_cart A N _105397)) (term156 A N _105396 _105397)). Qed.
Lemma lem7990278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7990279 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) : (term157 A N _105396 _105397) = (term158 A N _105396 _105397).
Proof. exact (MK_COMB (@lem7990278) (@lem7990268 A N _105396 _105397)). Qed.
Lemma lem7990289 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) : (term155 A N _105396 _105397) = (term155 A N _105396 _105397).
Proof. exact (eq_refl (term155 A N _105396 _105397)). Qed.
Lemma lem7990290 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) : ((term150 A N _105396 _105397) = (term155 A N _105396 _105397)) = ((term155 A N _105396 _105397) = (term155 A N _105396 _105397)).
Proof. exact (MK_COMB (@lem7990279 A N _105396 _105397) (@lem7990289 A N _105396 _105397)). Qed.
Lemma lem7990292 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7990293 (x : Prop) : (x = x) = True.
Proof. exact (@lem7990292 Prop x). Qed.
Lemma lem7990294 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) : ((term155 A N _105396 _105397) = (term155 A N _105396 _105397)) = True.
Proof. exact (@lem7990293 (term155 A N _105396 _105397)). Qed.
Lemma lem7990295 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) : ((term150 A N _105396 _105397) = (term155 A N _105396 _105397)) = True.
Proof. exact (TRANS (@lem7990290 A N _105396 _105397) (@lem7990294 A N _105396 _105397)). Qed.
Lemma lem7990296 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) : True = ((term150 A N _105396 _105397) = (term155 A N _105396 _105397)).
Proof. exact (SYM (@lem7990295 A N _105396 _105397)). Qed.
Lemma lem7990297 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) : (term150 A N _105396 _105397) = (term155 A N _105396 _105397).
Proof. exact (EQ_MP (@lem7990296 A N _105396 _105397) (@lem0)). Qed.
Lemma lem7990298 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) : term155 A N _105396 _105397.
Proof. exact (EQ_MP (@lem7990297 A N _105396 _105397) (@lem7990242 A N _105396 _105397)). Qed.
Lemma lem7990300 (b : Prop) (a : Prop) : (a \/ b) = (term159 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7990301 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) : (term155 A N _105396 _105397) = (term160 A N _105396 _105397).
Proof. exact (@lem7990300 (term156 A N _105396 _105397) ((@dest_cart A N _105396) = (@dest_cart A N _105397))). Qed.
Lemma lem7990303 (a : Prop) : (term161 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7990304 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) : (term162 A N _105396 _105397) = (_105396 = _105397).
Proof. exact (@lem7990303 (_105396 = _105397)). Qed.
Lemma lem7990305 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7990306 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) : (term163 A N _105396 _105397) = (term164 A N _105396 _105397).
Proof. exact (MK_COMB (@lem7990305) (@lem7990304 A N _105396 _105397)). Qed.
Lemma lem7990307 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) : ((@dest_cart A N _105396) = (@dest_cart A N _105397)) = ((@dest_cart A N _105396) = (@dest_cart A N _105397)).
Proof. exact (eq_refl ((@dest_cart A N _105396) = (@dest_cart A N _105397))). Qed.
Lemma lem7990308 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) : (term160 A N _105396 _105397) = (term148 A N _105396 _105397).
Proof. exact (MK_COMB (@lem7990306 A N _105396 _105397) (@lem7990307 A N _105396 _105397)). Qed.
Lemma lem7990309 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) : (term155 A N _105396 _105397) = (term148 A N _105396 _105397).
Proof. exact (TRANS (@lem7990301 A N _105396 _105397) (@lem7990308 A N _105396 _105397)). Qed.
Lemma lem7990312 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) : term148 A N _105396 _105397.
Proof. exact (EQ_MP (@lem7990309 A N _105396 _105397) (@lem7990298 A N _105396 _105397)). Qed.
Lemma lem7990313 {A N : Type'} (_105396 : cart A N) (_105397 : cart A N) : term148 A N _105396 _105397.
Proof. exact (@lem7990312 A N _105396 _105397). Qed.
Lemma lem7990314 {A N : Type'} (x : type35 A N) (y : type35 A N) : term165 A N x y.
Proof. exact (@lem7990313 A N (@mk_cart A N x) (@mk_cart A N y)). Qed.
Lemma lem7990317 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term130 A N x y) : (term116 A N x) = (term116 A N y).
Proof. exact (@lem7990314 A N x y (@lem7990261 A N x y h1)). Qed.
Lemma lem7990318 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term130 A N x y) : term166 A N x y.
Proof. exact (fun h0 : term167 A N x y => @lem7990317 A N x y h1). Qed.
Lemma lem7990320 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7990321 {A N : Type'} (x : type35 A N) (y : type35 A N) : (term166 A N x y) = ((term116 A N x) = (term116 A N y)).
Proof. exact (@lem7990320 ((term116 A N x) = (term116 A N y))). Qed.
Lemma lem7990322 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term130 A N x y) : (term116 A N x) = (term116 A N y).
Proof. exact (EQ_MP (@lem7990321 A N x y) (@lem7990318 A N x y h1)). Qed.
Lemma lem7990324 {A N : Type'} (_105395 : type35 A N) (h1 : term122 A N) : (term116 A N _105395) = _105395.
Proof. exact (EQ_MP (@lem7990225 A N _105395) (@lem7990224 A N _105395 h1)). Qed.
Lemma lem7990325 {A N : Type'} (_105395 : type35 A N) (h1 : term122 A N) : (term116 A N _105395) = _105395.
Proof. exact (@lem7990324 A N _105395 h1). Qed.
Lemma lem7990326 {A N : Type'} (x : type35 A N) (h1 : term122 A N) : (term116 A N x) = x.
Proof. exact (@lem7990325 A N x h1). Qed.
Lemma lem7990327 {A N : Type'} (x : type35 A N) (h1 : term122 A N) : term168 A N x.
Proof. exact (fun h0 : term169 A N x => @lem7990326 A N x h1). Qed.
Lemma lem7990329 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7990330 {A N : Type'} (x : type35 A N) : (term168 A N x) = ((term116 A N x) = x).
Proof. exact (@lem7990329 ((term116 A N x) = x)). Qed.
Lemma lem7990331 {A N : Type'} (x : type35 A N) (h1 : term122 A N) : (term116 A N x) = x.
Proof. exact (EQ_MP (@lem7990330 A N x) (@lem7990327 A N x h1)). Qed.
Lemma lem7990349 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7990350 {A N : Type'} (y : type35 A N) (x : type35 A N) (z : type35 A N) : (term170 A N x y z) = (term171 A N y x z).
Proof. exact (@lem7990349 (y = z) (term147 A N x z)). Qed.
Lemma lem7990360 {A N : Type'} (x : type35 A N) (y : type35 A N) : (term172 A N x y) = (term172 A N x y).
Proof. exact (eq_refl (term172 A N x y)). Qed.
Lemma lem7990361 {A N : Type'} (y : type35 A N) (x : type35 A N) (z : type35 A N) : (term151 A N x y z) = (term173 A N y x z).
Proof. exact (MK_COMB (@lem7990360 A N x y) (@lem7990350 A N y x z)). Qed.
Lemma lem7990365 (q : Prop) (p : Prop) (r : Prop) : (term174 p q r) = (term174 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7990366 {A N : Type'} (y : type35 A N) (x : type35 A N) (z : type35 A N) : (term173 A N y x z) = (term175 A N y x z).
Proof. exact (@lem7990365 (y = z) (term147 A N x y) (term147 A N x z)). Qed.
Lemma lem7990388 {A N : Type'} (y : type35 A N) (x : type35 A N) (z : type35 A N) : (term151 A N x y z) = (term175 A N y x z).
Proof. exact (TRANS (@lem7990361 A N y x z) (@lem7990366 A N y x z)). Qed.
Lemma lem7990389 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7990390 {A N : Type'} (y : type35 A N) (x : type35 A N) (z : type35 A N) : (term176 A N x y z) = (term177 A N y x z).
Proof. exact (MK_COMB (@lem7990389) (@lem7990388 A N y x z)). Qed.
Lemma lem7990412 {A N : Type'} (y : type35 A N) (x : type35 A N) (z : type35 A N) : (term175 A N y x z) = (term175 A N y x z).
Proof. exact (eq_refl (term175 A N y x z)). Qed.
Lemma lem7990413 {A N : Type'} (y : type35 A N) (x : type35 A N) (z : type35 A N) : ((term151 A N x y z) = (term175 A N y x z)) = ((term175 A N y x z) = (term175 A N y x z)).
Proof. exact (MK_COMB (@lem7990390 A N y x z) (@lem7990412 A N y x z)). Qed.
Lemma lem7990415 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7990416 (x : Prop) : (x = x) = True.
Proof. exact (@lem7990415 Prop x). Qed.
Lemma lem7990417 {A N : Type'} (y : type35 A N) (x : type35 A N) (z : type35 A N) : ((term175 A N y x z) = (term175 A N y x z)) = True.
Proof. exact (@lem7990416 (term175 A N y x z)). Qed.
Lemma lem7990418 {A N : Type'} (y : type35 A N) (x : type35 A N) (z : type35 A N) : ((term151 A N x y z) = (term175 A N y x z)) = True.
Proof. exact (TRANS (@lem7990413 A N y x z) (@lem7990417 A N y x z)). Qed.
Lemma lem7990419 {A N : Type'} (y : type35 A N) (x : type35 A N) (z : type35 A N) : True = ((term151 A N x y z) = (term175 A N y x z)).
Proof. exact (SYM (@lem7990418 A N y x z)). Qed.
Lemma lem7990420 {A N : Type'} (y : type35 A N) (x : type35 A N) (z : type35 A N) : (term151 A N x y z) = (term175 A N y x z).
Proof. exact (EQ_MP (@lem7990419 A N y x z) (@lem0)). Qed.
Lemma lem7990421 {A N : Type'} (y : type35 A N) (x : type35 A N) (z : type35 A N) : term175 A N y x z.
Proof. exact (EQ_MP (@lem7990420 A N y x z) (@lem7990254 A N x y z)). Qed.
Lemma lem7990423 (b : Prop) (a : Prop) : (a \/ b) = (term159 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7990424 {A N : Type'} (x : type35 A N) (y : type35 A N) (z : type35 A N) : (term175 A N y x z) = (term178 A N x y z).
Proof. exact (@lem7990423 (term179 A N y x z) (y = z)). Qed.
Lemma lem7990426 (a : Prop) (b : Prop) : (term180 a b) = (term181 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7990427 {A N : Type'} (y : type35 A N) (x : type35 A N) (z : type35 A N) : (term182 A N y x z) = (term183 A N y x z).
Proof. exact (@lem7990426 (term147 A N x y) (term147 A N x z)). Qed.
Lemma lem7990429 (a : Prop) : (term161 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7990430 {A N : Type'} (x : type35 A N) (y : type35 A N) : (term184 A N x y) = (x = y).
Proof. exact (@lem7990429 (x = y)). Qed.
Lemma lem7990431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7990432 {A N : Type'} (x : type35 A N) (y : type35 A N) : (term185 A N x y) = (term186 A N x y).
Proof. exact (MK_COMB (@lem7990431) (@lem7990430 A N x y)). Qed.
Lemma lem7990434 (a : Prop) : (term161 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7990435 {A N : Type'} (x : type35 A N) (z : type35 A N) : (term184 A N x z) = (x = z).
Proof. exact (@lem7990434 (x = z)). Qed.
Lemma lem7990436 {A N : Type'} (y : type35 A N) (x : type35 A N) (z : type35 A N) : (term183 A N y x z) = (term187 A N y x z).
Proof. exact (MK_COMB (@lem7990432 A N x y) (@lem7990435 A N x z)). Qed.
Lemma lem7990437 {A N : Type'} (y : type35 A N) (x : type35 A N) (z : type35 A N) : (term182 A N y x z) = (term187 A N y x z).
Proof. exact (TRANS (@lem7990427 A N y x z) (@lem7990436 A N y x z)). Qed.
Lemma lem7990438 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7990439 {A N : Type'} (y : type35 A N) (x : type35 A N) (z : type35 A N) : (term188 A N y x z) = (term189 A N y x z).
Proof. exact (MK_COMB (@lem7990438) (@lem7990437 A N y x z)). Qed.
Lemma lem7990440 {A N : Type'} (y : type35 A N) (z : type35 A N) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7990441 {A N : Type'} (x : type35 A N) (y : type35 A N) (z : type35 A N) : (term178 A N x y z) = (term190 A N x y z).
Proof. exact (MK_COMB (@lem7990439 A N y x z) (@lem7990440 A N y z)). Qed.
Lemma lem7990442 {A N : Type'} (x : type35 A N) (y : type35 A N) (z : type35 A N) : (term175 A N y x z) = (term190 A N x y z).
Proof. exact (TRANS (@lem7990424 A N x y z) (@lem7990441 A N x y z)). Qed.
Lemma lem7990444 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term122 A N) (h2 : term130 A N x y) : term191 A N y x.
Proof. exact (conj (@lem7990322 A N x y h2) (@lem7990331 A N x h1)). Qed.
Lemma lem7990446 {A N : Type'} (x : type35 A N) (y : type35 A N) (z : type35 A N) : term190 A N x y z.
Proof. exact (EQ_MP (@lem7990442 A N x y z) (@lem7990421 A N y x z)). Qed.
Lemma lem7990447 {A N : Type'} (x : type35 A N) (y : type35 A N) (z : type35 A N) : term190 A N x y z.
Proof. exact (@lem7990446 A N x y z). Qed.
Lemma lem7990448 {A N : Type'} (y : type35 A N) (x : type35 A N) : term192 A N y x.
Proof. exact (@lem7990447 A N (term116 A N x) (term116 A N y) x). Qed.
Lemma lem7990451 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term122 A N) (h2 : term130 A N x y) : (term116 A N y) = x.
Proof. exact (@lem7990448 A N y x (@lem7990444 A N x y h1 h2)). Qed.
Lemma lem7990452 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term122 A N) (h2 : term130 A N x y) : term193 A N y x.
Proof. exact (fun h0 : term194 A N y x => @lem7990451 A N x y h1 h2). Qed.
Lemma lem7990454 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7990455 {A N : Type'} (y : type35 A N) (x : type35 A N) : (term193 A N y x) = ((term116 A N y) = x).
Proof. exact (@lem7990454 ((term116 A N y) = x)). Qed.
Lemma lem7990456 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term122 A N) (h2 : term130 A N x y) : (term116 A N y) = x.
Proof. exact (EQ_MP (@lem7990455 A N y x) (@lem7990452 A N x y h1 h2)). Qed.
Lemma lem7990458 {A N : Type'} (_105395 : type35 A N) (h1 : term122 A N) : (term116 A N _105395) = _105395.
Proof. exact (EQ_MP (@lem7990225 A N _105395) (@lem7990224 A N _105395 h1)). Qed.
Lemma lem7990459 {A N : Type'} (_105395 : type35 A N) (h1 : term122 A N) : (term116 A N _105395) = _105395.
Proof. exact (@lem7990458 A N _105395 h1). Qed.
Lemma lem7990460 {A N : Type'} (y : type35 A N) (h1 : term122 A N) : (term116 A N y) = y.
Proof. exact (@lem7990459 A N y h1). Qed.
Lemma lem7990461 {A N : Type'} (y : type35 A N) (h1 : term122 A N) : term168 A N y.
Proof. exact (fun h0 : term169 A N y => @lem7990460 A N y h1). Qed.
Lemma lem7990463 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7990464 {A N : Type'} (y : type35 A N) : (term168 A N y) = ((term116 A N y) = y).
Proof. exact (@lem7990463 ((term116 A N y) = y)). Qed.
Lemma lem7990465 {A N : Type'} (y : type35 A N) (h1 : term122 A N) : (term116 A N y) = y.
Proof. exact (EQ_MP (@lem7990464 A N y) (@lem7990461 A N y h1)). Qed.
Lemma lem7990466 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term122 A N) (h2 : term130 A N x y) : term195 A N x y.
Proof. exact (conj (@lem7990456 A N x y h1 h2) (@lem7990465 A N y h1)). Qed.
Lemma lem7990468 {A N : Type'} (x : type35 A N) (y : type35 A N) (z : type35 A N) : term190 A N x y z.
Proof. exact (EQ_MP (@lem7990442 A N x y z) (@lem7990421 A N y x z)). Qed.
Lemma lem7990469 {A N : Type'} (x : type35 A N) (y : type35 A N) (z : type35 A N) : term190 A N x y z.
Proof. exact (@lem7990468 A N x y z). Qed.
Lemma lem7990470 {A N : Type'} (x : type35 A N) (y : type35 A N) : term196 A N x y.
Proof. exact (@lem7990469 A N (term116 A N y) x y). Qed.
Lemma lem7990473 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term122 A N) (h2 : term130 A N x y) : x = y.
Proof. exact (@lem7990470 A N x y (@lem7990466 A N x y h1 h2)). Qed.
Lemma lem7990474 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term122 A N) (h2 : term130 A N x y) : term197 A N x y.
Proof. exact (fun h0 : term147 A N x y => @lem7990473 A N x y h1 h2). Qed.
Lemma lem7990476 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7990477 {A N : Type'} (x : type35 A N) (y : type35 A N) : (term197 A N x y) = (x = y).
Proof. exact (@lem7990476 (x = y)). Qed.
Lemma lem7990478 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term122 A N) (h2 : term130 A N x y) : x = y.
Proof. exact (EQ_MP (@lem7990477 A N x y) (@lem7990474 A N x y h1 h2)). Qed.
Lemma lem7990481 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7990483 {A N : Type'} (x : type35 A N) (y : type35 A N) : (term147 A N x y) = (term198 A N x y).
Proof. exact (@lem7990481 (x = y)). Qed.
Lemma lem7990486 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term130 A N x y) : term198 A N x y.
Proof. exact (EQ_MP (@lem7990483 A N x y) (@lem7990230 A N x y h1)). Qed.
Lemma lem7990489 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term122 A N) (h2 : term130 A N x y) : False.
Proof. exact (@lem7990486 A N x y h2 (@lem7990478 A N x y h1 h2)). Qed.
Lemma lem7990490 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term122 A N) (h2 : term130 A N x y) : term199.
Proof. exact (fun h0 : ~ False => @lem7990489 A N x y h1 h2). Qed.
Lemma lem7990492 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7990493 : term199 = False.
Proof. exact (@lem7990492 False). Qed.
Lemma lem7990494 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term122 A N) (h2 : term130 A N x y) : False.
Proof. exact (EQ_MP (@lem7990493) (@lem7990490 A N x y h1 h2)). Qed.
Lemma lem7990495 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term122 A N) (h2 : term130 A N x y) : (term130 A N x y) = False.
Proof. exact (prop_ext (fun h3 : term130 A N x y => @lem7990494 A N x y h1 h2) (fun h3 : False => @lem7990194 A N x y h2)). Qed.
Lemma lem7990496 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term122 A N) (h2 : term130 A N x y) : False.
Proof. exact (EQ_MP (@lem7990495 A N x y h1 h2) (@lem7990194 A N x y h2)). Qed.
Lemma lem7990497 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term122 A N) (h2 : term130 A N x y) : (term122 A N) = False.
Proof. exact (prop_ext (fun h3 : term122 A N => @lem7990496 A N x y h1 h2) (fun h3 : False => @lem7990174 A N h1)). Qed.
Lemma lem7990498 {A N : Type'} (x : type35 A N) (y : type35 A N) (h1 : term122 A N) (h2 : term130 A N x y) : False.
Proof. exact (EQ_MP (@lem7990497 A N x y h1 h2) (@lem7990174 A N h1)). Qed.
Lemma lem7990499 {A N : Type'} (x : type35 A N) (h1 : term139 A N x) (h2 : term122 A N) : False.
Proof. exact (ex_elim (@lem7990145 A N x h1) (fun y : type35 A N => fun h0 : term138 A N x y => @lem7990498 A N x y h2 h0)). Qed.
Lemma lem7990500 {A N : Type'} (h1 : term108 A N) (h2 : term122 A N) : False.
Proof. exact (ex_elim (@lem7990120 A N h1) (fun x : type35 A N => fun h0 : term144 A N x => @lem7990499 A N x h0 h2)). Qed.
Lemma lem7990501 {A N : Type'} (h1 : term108 A N) (h2 : term122 A N) : (term122 A N) = False.
Proof. exact (prop_ext (fun h3 : term122 A N => @lem7990500 A N h1 h2) (fun h3 : False => @lem7990144 A N h2)). Qed.
Lemma lem7990502 {A N : Type'} (h1 : term108 A N) (h2 : term122 A N) : False.
Proof. exact (EQ_MP (@lem7990501 A N h1 h2) (@lem7990144 A N h2)). Qed.
Lemma lem7990503 {A N : Type'} (h1 : term108 A N) : term200 A N.
Proof. exact (fun h0 : term122 A N => @lem7990502 A N h1 h0). Qed.
Lemma lem7990504 {A N : Type'} : (term200 A N) = (term123 A N).
Proof. exact (@lem69 (term122 A N)). Qed.
Lemma lem7990505 {A N : Type'} (h1 : term108 A N) : term123 A N.
Proof. exact (EQ_MP (@lem7990504 A N) (@lem7990503 A N h1)). Qed.
Lemma lem7990506 {A N : Type'} : term125 A N.
Proof. exact (fun h0 : term108 A N => @lem7990505 A N h0). Qed.
Lemma lem7990507 {A N : Type'} : term110 A N.
Proof. exact (EQ_MP (@lem7990034 A N) (@lem7990506 A N)). Qed.
Lemma lem7990509 {A N : Type'} : term110 A N.
Proof. exact (@lem7989921 A N (@lem7990507 A N)). Qed.
Lemma lem7990510 {A N : Type'} (h1 : term108 A N) : term114 A N.
Proof. exact (@lem7990509 A N (@lem7989902 A N h1)). Qed.
Lemma lem7990511 {A N : Type'} (h1 : term108 A N) : False.
Proof. exact (@lem7990510 A N h1 (@lem7989903 A N)). Qed.
Lemma lem7990512 {A N : Type'} (h1 : term108 A N) : (term108 A N) = False.
Proof. exact (prop_ext (fun h2 : term108 A N => @lem7990511 A N h1) (fun h2 : False => @lem7989902 A N h1)). Qed.
Lemma lem7990513 {A N : Type'} (h1 : term108 A N) : False.
Proof. exact (EQ_MP (@lem7990512 A N h1) (@lem7989902 A N h1)). Qed.
Lemma lem7990514 {A N : Type'} : term107 A N.
Proof. exact (fun h0 : term108 A N => @lem7990513 A N h0). Qed.
Lemma lem7990515 {A N : Type'} : term94 A N.
Proof. exact (EQ_MP (@lem7989901 A N) (@lem7990514 A N)). Qed.
Lemma lem7990517 (a : Prop) (b : Prop) : term9 a b.
Proof. exact (@lem7989620 a b (@lem1157 a b)). Qed.
Lemma lem7990518 {A N : Type'} (m : nat) : term201 A N m.
Proof. exact (@lem7990517 (term97 A N m) (term101 A N m)). Qed.
Lemma lem7990519 {N : Type'} (m : nat) : (term75 N m) = (term75 N m).
Proof. exact (eq_refl (term75 N m)). Qed.
Lemma lem7990520 {A N : Type'} : (@HAS_SIZE (cart A N)) = (@HAS_SIZE (cart A N)).
Proof. exact (eq_refl (@HAS_SIZE (cart A N))). Qed.
Lemma lem7990522 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) : term5 _88266 _88270 f s t.
Proof. exact (EQ_MP (@lem7989611 _88266 _88270 f s t) (@lem7989610 _88266 _88270 f s t)). Qed.
Lemma lem7990523 {A N : Type'} (f : type61 A N) (s : type62 A N) (t : type24 A N) : term202 A N f s t.
Proof. exact (@lem7990522 (cart A N) (type35 A N) f s t). Qed.
Lemma lem7990524 {A N : Type'} : term203 A N.
Proof. exact (@lem7990523 A N (@mk_cart A N) (@UNIV ((finite_image N) -> A)) (@UNIV (cart A N))). Qed.
Lemma lem7990534 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem7989588 A x) (@lem7989587 A x)). Qed.
Lemma lem7990535 {A N : Type'} (x : cart A N) : (@IN (cart A N) x (@UNIV (cart A N))) = True.
Proof. exact (@lem7990534 (cart A N) x). Qed.
Lemma lem7990536 {A N : Type'} (y : cart A N) : (@IN (cart A N) y (@UNIV (cart A N))) = True.
Proof. exact (@lem7990535 A N y). Qed.
Lemma lem7990537 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7990538 {A N : Type'} (y : cart A N) : (term204 A N y) = (imp True).
Proof. exact (MK_COMB (@lem7990537) (@lem7990536 A N y)). Qed.
Lemma lem7990545 {A N : Type'} (y : cart A N) : (term205 A N y) = (term205 A N y).
Proof. exact (eq_refl (term205 A N y)). Qed.
Lemma lem7990546 {A N : Type'} (y : cart A N) : (term206 A N y) = (term207 A N y).
Proof. exact (MK_COMB (@lem7990538 A N y) (@lem7990545 A N y)). Qed.
Lemma lem7990548 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem7990549 {A N : Type'} (y : cart A N) : (term207 A N y) = (term205 A N y).
Proof. exact (@lem7990548 (term205 A N y)). Qed.
Lemma lem7990556 {A N : Type'} (y : cart A N) : (term206 A N y) = (term205 A N y).
Proof. exact (TRANS (@lem7990546 A N y) (@lem7990549 A N y)). Qed.
Lemma lem7990557 {A N : Type'} : (term208 A N) = (term209 A N).
Proof. exact (fun_ext (fun y : cart A N => @lem7990556 A N y)). Qed.
Lemma lem7990558 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem7990559 {A N : Type'} : (term210 A N) = (term211 A N).
Proof. exact (MK_COMB (@lem7990558 A N) (@lem7990557 A N)). Qed.
Lemma lem7990564 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7990565 {A N : Type'} : (term212 A N) = (term213 A N).
Proof. exact (MK_COMB (@lem7990564) (@lem7990559 A N)). Qed.
Lemma lem7990573 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem7989588 A x) (@lem7989587 A x)). Qed.
Lemma lem7990574 {A N : Type'} (x : cart A N) : (@IN (cart A N) x (@UNIV (cart A N))) = True.
Proof. exact (@lem7990573 (cart A N) x). Qed.
Lemma lem7990575 {A N : Type'} (x : type35 A N) : (term214 A N x) = True.
Proof. exact (@lem7990574 A N (@mk_cart A N x)). Qed.
Lemma lem7990576 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7990577 {A N : Type'} (x : type35 A N) : (term215 A N x) = (@eq Prop True).
Proof. exact (MK_COMB (@lem7990576) (@lem7990575 A N x)). Qed.
Lemma lem7990579 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem7989588 A x) (@lem7989587 A x)). Qed.
Lemma lem7990580 {A N : Type'} (x : type35 A N) : (@IN ((finite_image N) -> A) x (@UNIV ((finite_image N) -> A))) = True.
Proof. exact (@lem7990579 (type35 A N) x). Qed.
Lemma lem7990581 {A N : Type'} (x : type35 A N) : ((term214 A N x) = (@IN ((finite_image N) -> A) x (@UNIV ((finite_image N) -> A)))) = (True = True).
Proof. exact (MK_COMB (@lem7990577 A N x) (@lem7990580 A N x)). Qed.
Lemma lem7990583 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem7990584 : (True = True) = True.
Proof. exact (@lem7990583 True). Qed.
Lemma lem7990585 {A N : Type'} (x : type35 A N) : ((term214 A N x) = (@IN ((finite_image N) -> A) x (@UNIV ((finite_image N) -> A)))) = True.
Proof. exact (TRANS (@lem7990581 A N x) (@lem7990584)). Qed.
Lemma lem7990586 {A N : Type'} : (term216 A N) = (term217 A N).
Proof. exact (fun_ext (fun x : type35 A N => @lem7990585 A N x)). Qed.
Lemma lem7990587 {A N : Type'} : (@all ((finite_image N) -> A)) = (@all ((finite_image N) -> A)).
Proof. exact (eq_refl (@all ((finite_image N) -> A))). Qed.
Lemma lem7990588 {A N : Type'} : (term218 A N) = (term219 A N).
Proof. exact (MK_COMB (@lem7990587 A N) (@lem7990586 A N)). Qed.
Lemma lem7990590 {A : Type'} (t : Prop) : (term220 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7990591 {A N : Type'} (t : Prop) : (term221 A N t) = t.
Proof. exact (@lem7990590 (type35 A N) t). Qed.
Lemma lem7990592 {A N : Type'} : (term219 A N) = True.
Proof. exact (@lem7990591 A N True). Qed.
Lemma lem7990593 {A N : Type'} : (term218 A N) = True.
Proof. exact (TRANS (@lem7990588 A N) (@lem7990592 A N)). Qed.
Lemma lem7990594 {A N : Type'} : (term222 A N) = (term223 A N).
Proof. exact (MK_COMB (@lem7990565 A N) (@lem7990593 A N)). Qed.
Lemma lem7990596 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem7990597 {A N : Type'} : (term223 A N) = (term211 A N).
Proof. exact (@lem7990596 (term211 A N)). Qed.
Lemma lem7990608 {A N : Type'} : (term222 A N) = (term211 A N).
Proof. exact (TRANS (@lem7990594 A N) (@lem7990597 A N)). Qed.
Lemma lem7990609 {A N : Type'} : (term211 A N) = (term222 A N).
Proof. exact (SYM (@lem7990608 A N)). Qed.
Lemma lem7990611 (p : Prop) : p = (term106 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7990612 {A N : Type'} : (term211 A N) = (term224 A N).
Proof. exact (@lem7990611 (term211 A N)). Qed.
Lemma lem7990613 {A N : Type'} : (term224 A N) = (term211 A N).
Proof. exact (SYM (@lem7990612 A N)). Qed.
Lemma lem7990614 {A N : Type'} (h1 : term225 A N) : term225 A N.
Proof. exact (h1). Qed.
Lemma lem7990615 {A N : Type'} : term109 A N.
Proof. exact (@lem7614851 A N). Qed.
Lemma lem7990619 {A N : Type'} (h1 : term226 A N) : term226 A N.
Proof. exact (h1). Qed.
Lemma lem7990620 {A N : Type'} : term227 A N.
Proof. exact (fun h0 : term226 A N => @lem7990619 A N h0). Qed.
Lemma lem7990621 {A N : Type'} (h1 : term227 A N) : term227 A N.
Proof. exact (h1). Qed.
Lemma lem7990622 {A N : Type'} (h1 : term226 A N) : term226 A N.
Proof. exact (h1). Qed.
Lemma lem7990623 {A N : Type'} (h1 : term226 A N) (h2 : term227 A N) : term226 A N.
Proof. exact (@lem7990621 A N h2 (@lem7990622 A N h1)). Qed.
Lemma lem7990624 {A N : Type'} (h1 : term226 A N) : term228 A N.
Proof. exact (fun h0 : term227 A N => @lem7990623 A N h1 h0). Qed.
Lemma lem7990625 {A N : Type'} (h1 : term227 A N) : term227 A N.
Proof. exact (h1). Qed.
Lemma lem7990626 {A N : Type'} (h1 : term226 A N) (h2 : term227 A N) : term226 A N.
Proof. exact (@lem7990624 A N h1 (@lem7990625 A N h2)). Qed.
Lemma lem7990627 {A N : Type'} (h1 : term227 A N) : term227 A N.
Proof. exact (fun h0 : term226 A N => @lem7990626 A N h0 h1). Qed.
Lemma lem7990628 {A N : Type'} : term229 A N.
Proof. exact (fun h0 : term227 A N => @lem7990627 A N h0). Qed.
Lemma lem7990631 {A N : Type'} : term227 A N.
Proof. exact (@lem7990628 A N (@lem7990620 A N)). Qed.
Lemma lem7990632 {A N : Type'} : term227 A N.
Proof. exact (@lem7990631 A N). Qed.
Lemma lem7990644 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7990645 {A N : Type'} : (term114 A N) = (term115 A N).
Proof. exact (@lem7990644 (term109 A N)). Qed.
Lemma lem7990657 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem16462 t)). Qed.
Lemma lem7990658 {A N : Type'} (r : type35 A N) : (True = ((term116 A N r) = r)) = ((term116 A N r) = r).
Proof. exact (@lem7990657 ((term116 A N r) = r)). Qed.
Lemma lem7990659 {A N : Type'} : (term117 A N) = (term118 A N).
Proof. exact (fun_ext (fun r : type35 A N => @lem7990658 A N r)). Qed.
Lemma lem7990660 {A N : Type'} : (@all ((finite_image N) -> A)) = (@all ((finite_image N) -> A)).
Proof. exact (eq_refl (@all ((finite_image N) -> A))). Qed.
Lemma lem7990661 {A N : Type'} : (term119 A N) = (term120 A N).
Proof. exact (MK_COMB (@lem7990660 A N) (@lem7990659 A N)). Qed.
Lemma lem7990666 {A N : Type'} : (term121 A N) = (term121 A N).
Proof. exact (eq_refl (term121 A N)). Qed.
Lemma lem7990667 {A N : Type'} : (term109 A N) = (term122 A N).
Proof. exact (MK_COMB (@lem7990666 A N) (@lem7990661 A N)). Qed.
Lemma lem7990670 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7990671 {A N : Type'} : (term115 A N) = (term123 A N).
Proof. exact (MK_COMB (@lem7990670) (@lem7990667 A N)). Qed.
Lemma lem7990672 {A N : Type'} : (term114 A N) = (term123 A N).
Proof. exact (TRANS (@lem7990645 A N) (@lem7990671 A N)). Qed.
Lemma lem7990673 {A N : Type'} : (term230 A N) = (term230 A N).
Proof. exact (eq_refl (term230 A N)). Qed.
Lemma lem7990680 {A N : Type'} : (term226 A N) = (term231 A N).
Proof. exact (MK_COMB (@lem7990673 A N) (@lem7990672 A N)). Qed.
Lemma lem7990681 {A N : Type'} (r : type35 A N) : ((term116 A N r) = r) = ((term116 A N r) = r).
Proof. exact (eq_refl ((term116 A N r) = r)). Qed.
Lemma lem7990682 {A N : Type'} : (term118 A N) = (term118 A N).
Proof. exact (fun_ext (fun r : type35 A N => @lem7990681 A N r)). Qed.
Lemma lem7990683 {A N : Type'} : (@all ((finite_image N) -> A)) = (@all ((finite_image N) -> A)).
Proof. exact (eq_refl (@all ((finite_image N) -> A))). Qed.
Lemma lem7990684 {A N : Type'} : (term120 A N) = (term120 A N).
Proof. exact (MK_COMB (@lem7990683 A N) (@lem7990682 A N)). Qed.
Lemma lem7990685 {A N : Type'} (a : cart A N) : ((term126 A N a) = a) = ((term126 A N a) = a).
Proof. exact (eq_refl ((term126 A N a) = a)). Qed.
Lemma lem7990686 {A N : Type'} : (term127 A N) = (term127 A N).
Proof. exact (fun_ext (fun a : cart A N => @lem7990685 A N a)). Qed.
Lemma lem7990687 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem7990688 {A N : Type'} : (term128 A N) = (term128 A N).
Proof. exact (MK_COMB (@lem7990687 A N) (@lem7990686 A N)). Qed.
Lemma lem7990689 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7990690 {A N : Type'} : (term121 A N) = (term121 A N).
Proof. exact (MK_COMB (@lem7990689) (@lem7990688 A N)). Qed.
Lemma lem7990691 {A N : Type'} : (term122 A N) = (term122 A N).
Proof. exact (MK_COMB (@lem7990690 A N) (@lem7990684 A N)). Qed.
Lemma lem7990692 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7990693 {A N : Type'} : (term123 A N) = (term123 A N).
Proof. exact (MK_COMB (@lem7990692) (@lem7990691 A N)). Qed.
Lemma lem7990694 {A N : Type'} (x : type35 A N) (y : cart A N) : ((@mk_cart A N x) = y) = ((@mk_cart A N x) = y).
Proof. exact (eq_refl ((@mk_cart A N x) = y)). Qed.
Lemma lem7990695 {A N : Type'} (y : cart A N) : (term232 A N y) = (term232 A N y).
Proof. exact (fun_ext (fun x : type35 A N => @lem7990694 A N x y)). Qed.
Lemma lem7990696 {A N : Type'} : (@ex ((finite_image N) -> A)) = (@ex ((finite_image N) -> A)).
Proof. exact (eq_refl (@ex ((finite_image N) -> A))). Qed.
Lemma lem7990697 {A N : Type'} (y : cart A N) : (term205 A N y) = (term205 A N y).
Proof. exact (MK_COMB (@lem7990696 A N) (@lem7990695 A N y)). Qed.
Lemma lem7990698 {A N : Type'} : (term209 A N) = (term209 A N).
Proof. exact (fun_ext (fun y : cart A N => @lem7990697 A N y)). Qed.
Lemma lem7990699 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem7990700 {A N : Type'} : (term211 A N) = (term211 A N).
Proof. exact (MK_COMB (@lem7990699 A N) (@lem7990698 A N)). Qed.
Lemma lem7990701 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7990702 {A N : Type'} : (term225 A N) = (term225 A N).
Proof. exact (MK_COMB (@lem7990701) (@lem7990700 A N)). Qed.
Lemma lem7990703 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7990704 {A N : Type'} : (term230 A N) = (term230 A N).
Proof. exact (MK_COMB (@lem7990703) (@lem7990702 A N)). Qed.
Lemma lem7990705 {A N : Type'} : (term231 A N) = (term231 A N).
Proof. exact (MK_COMB (@lem7990704 A N) (@lem7990693 A N)). Qed.
Lemma lem7990736 {A N : Type'} : (term226 A N) = (term231 A N).
Proof. exact (TRANS (@lem7990680 A N) (@lem7990705 A N)). Qed.
Lemma lem7990737 {A N : Type'} : (term231 A N) = (term226 A N).
Proof. exact (SYM (@lem7990736 A N)). Qed.
Lemma lem7990738 {A N : Type'} (h1 : term225 A N) : term225 A N.
Proof. exact (h1). Qed.
Lemma lem7990739 {A N : Type'} (h1 : term122 A N) : term122 A N.
Proof. exact (h1). Qed.
Lemma lem7990741 {A N : Type'} (P : type62 A N) : (term233 A N P) = (term234 A N P).
Proof. exact (@lem18394 (type35 A N) P). Qed.
Lemma lem7990742 {A N : Type'} (y : cart A N) : (term235 A N y) = (term236 A N y).
Proof. exact (@lem7990741 A N (term232 A N y)). Qed.
Lemma lem7990743 {A N : Type'} (x : type35 A N) (y : cart A N) : (term237 A N y x) = ((@mk_cart A N x) = y).
Proof. exact (eq_refl (term237 A N y x)). Qed.
Lemma lem7990744 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7990746 {A N : Type'} (x : type35 A N) (y : cart A N) : (term238 A N y x) = (term239 A N x y).
Proof. exact (MK_COMB (@lem7990744) (@lem7990743 A N x y)). Qed.
Lemma lem7990747 {A N : Type'} (y : cart A N) : (term240 A N y) = (term241 A N y).
Proof. exact (fun_ext (fun x : type35 A N => @lem7990746 A N x y)). Qed.
Lemma lem7990748 {A N : Type'} : (@all ((finite_image N) -> A)) = (@all ((finite_image N) -> A)).
Proof. exact (eq_refl (@all ((finite_image N) -> A))). Qed.
Lemma lem7990749 {A N : Type'} (y : cart A N) : (term236 A N y) = (term242 A N y).
Proof. exact (MK_COMB (@lem7990748 A N) (@lem7990747 A N y)). Qed.
Lemma lem7990750 {A N : Type'} (y : cart A N) : (term235 A N y) = (term242 A N y).
Proof. exact (TRANS (@lem7990742 A N y) (@lem7990749 A N y)). Qed.
Lemma lem7990751 {A N : Type'} (P : type24 A N) : (term243 A N P) = (term244 A N P).
Proof. exact (@lem18392 (cart A N) P). Qed.
Lemma lem7990752 {A N : Type'} : (term225 A N) = (term245 A N).
Proof. exact (@lem7990751 A N (term209 A N)). Qed.
Lemma lem7990753 {A N : Type'} (y : cart A N) : (term246 A N y) = (term205 A N y).
Proof. exact (eq_refl (term246 A N y)). Qed.
Lemma lem7990754 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7990755 {A N : Type'} (y : cart A N) : (term247 A N y) = (term235 A N y).
Proof. exact (MK_COMB (@lem7990754) (@lem7990753 A N y)). Qed.
Lemma lem7990756 {A N : Type'} (y : cart A N) : (term247 A N y) = (term242 A N y).
Proof. exact (TRANS (@lem7990755 A N y) (@lem7990750 A N y)). Qed.
Lemma lem7990757 {A N : Type'} : (term248 A N) = (term249 A N).
Proof. exact (fun_ext (fun y : cart A N => @lem7990756 A N y)). Qed.
Lemma lem7990758 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem7990759 {A N : Type'} : (term245 A N) = (term250 A N).
Proof. exact (MK_COMB (@lem7990758 A N) (@lem7990757 A N)). Qed.
Lemma lem7990772 {A N : Type'} : (term225 A N) = (term250 A N).
Proof. exact (TRANS (@lem7990752 A N) (@lem7990759 A N)). Qed.
Lemma lem7990773 {A N : Type'} (h1 : term225 A N) : term250 A N.
Proof. exact (EQ_MP (@lem7990772 A N) (@lem7990738 A N h1)). Qed.
Lemma lem7990774 {A N : Type'} (a : cart A N) : ((term126 A N a) = a) = ((term126 A N a) = a).
Proof. exact (eq_refl ((term126 A N a) = a)). Qed.
Lemma lem7990775 {A N : Type'} : (term127 A N) = (term127 A N).
Proof. exact (fun_ext (fun a : cart A N => @lem7990774 A N a)). Qed.
Lemma lem7990776 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem7990777 {A N : Type'} : (term128 A N) = (term128 A N).
Proof. exact (MK_COMB (@lem7990776 A N) (@lem7990775 A N)). Qed.
Lemma lem7990778 {A N : Type'} (r : type35 A N) : ((term116 A N r) = r) = ((term116 A N r) = r).
Proof. exact (eq_refl ((term116 A N r) = r)). Qed.
Lemma lem7990779 {A N : Type'} : (term118 A N) = (term118 A N).
Proof. exact (fun_ext (fun r : type35 A N => @lem7990778 A N r)). Qed.
Lemma lem7990780 {A N : Type'} : (@all ((finite_image N) -> A)) = (@all ((finite_image N) -> A)).
Proof. exact (eq_refl (@all ((finite_image N) -> A))). Qed.
Lemma lem7990781 {A N : Type'} : (term120 A N) = (term120 A N).
Proof. exact (MK_COMB (@lem7990780 A N) (@lem7990779 A N)). Qed.
Lemma lem7990782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7990783 {A N : Type'} : (term121 A N) = (term121 A N).
Proof. exact (MK_COMB (@lem7990782) (@lem7990777 A N)). Qed.
Lemma lem7990796 {A N : Type'} : (term122 A N) = (term122 A N).
Proof. exact (MK_COMB (@lem7990783 A N) (@lem7990781 A N)). Qed.
Lemma lem7990797 {A N : Type'} (h1 : term122 A N) : term122 A N.
Proof. exact (EQ_MP (@lem7990796 A N) (@lem7990739 A N h1)). Qed.
Lemma lem7990798 {A N : Type'} (y : cart A N) (h1 : term242 A N y) : term242 A N y.
Proof. exact (h1). Qed.
Lemma lem7990807 {A N : Type'} (r : type35 A N) : ((term116 A N r) = r) = ((term116 A N r) = r).
Proof. exact (eq_refl ((term116 A N r) = r)). Qed.
Lemma lem7990808 {A N : Type'} : (term118 A N) = (term118 A N).
Proof. exact (fun_ext (fun r : type35 A N => @lem7990807 A N r)). Qed.
Lemma lem7990809 {A N : Type'} : (@all ((finite_image N) -> A)) = (@all ((finite_image N) -> A)).
Proof. exact (eq_refl (@all ((finite_image N) -> A))). Qed.
Lemma lem7990810 {A N : Type'} : (term120 A N) = (term120 A N).
Proof. exact (MK_COMB (@lem7990809 A N) (@lem7990808 A N)). Qed.
Lemma lem7990819 {A N : Type'} (a : cart A N) : ((term126 A N a) = a) = ((term126 A N a) = a).
Proof. exact (eq_refl ((term126 A N a) = a)). Qed.
Lemma lem7990820 {A N : Type'} : (term127 A N) = (term127 A N).
Proof. exact (fun_ext (fun a : cart A N => @lem7990819 A N a)). Qed.
Lemma lem7990821 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem7990822 {A N : Type'} : (term128 A N) = (term128 A N).
Proof. exact (MK_COMB (@lem7990821 A N) (@lem7990820 A N)). Qed.
Lemma lem7990823 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7990824 {A N : Type'} : (term121 A N) = (term121 A N).
Proof. exact (MK_COMB (@lem7990823) (@lem7990822 A N)). Qed.
Lemma lem7990825 {A N : Type'} : (term122 A N) = (term122 A N).
Proof. exact (MK_COMB (@lem7990824 A N) (@lem7990810 A N)). Qed.
Lemma lem7990826 {A N : Type'} (h1 : term122 A N) : term122 A N.
Proof. exact (EQ_MP (@lem7990825 A N) (@lem7990797 A N h1)). Qed.
Lemma lem7990835 {A N : Type'} (x : type35 A N) (y : cart A N) : (term239 A N x y) = (term239 A N x y).
Proof. exact (eq_refl (term239 A N x y)). Qed.
Lemma lem7990836 {A N : Type'} (y : cart A N) : (term241 A N y) = (term241 A N y).
Proof. exact (fun_ext (fun x : type35 A N => @lem7990835 A N x y)). Qed.
Lemma lem7990837 {A N : Type'} : (@all ((finite_image N) -> A)) = (@all ((finite_image N) -> A)).
Proof. exact (eq_refl (@all ((finite_image N) -> A))). Qed.
Lemma lem7990838 {A N : Type'} (y : cart A N) : (term242 A N y) = (term242 A N y).
Proof. exact (MK_COMB (@lem7990837 A N) (@lem7990836 A N y)). Qed.
Lemma lem7990839 {A N : Type'} (y : cart A N) (h1 : term242 A N y) : term242 A N y.
Proof. exact (EQ_MP (@lem7990838 A N y) (@lem7990798 A N y h1)). Qed.
Lemma lem7990841 {A N : Type'} (h1 : term122 A N) : term128 A N.
Proof. exact (proj1 (@lem7990826 A N h1)). Qed.
Lemma lem7990843 {A N : Type'} (x : type35 A N) (y : cart A N) : (term239 A N x y) = (term239 A N x y).
Proof. exact (eq_refl (term239 A N x y)). Qed.
Lemma lem7990844 {A N : Type'} (y : cart A N) : (term241 A N y) = (term241 A N y).
Proof. exact (fun_ext (fun x : type35 A N => @lem7990843 A N x y)). Qed.
Lemma lem7990845 {A N : Type'} : (@all ((finite_image N) -> A)) = (@all ((finite_image N) -> A)).
Proof. exact (eq_refl (@all ((finite_image N) -> A))). Qed.
Lemma lem7990847 {A N : Type'} (y : cart A N) : (term242 A N y) = (term242 A N y).
Proof. exact (MK_COMB (@lem7990845 A N) (@lem7990844 A N y)). Qed.
Lemma lem7990848 {A N : Type'} (y : cart A N) (h1 : term242 A N y) : term242 A N y.
Proof. exact (EQ_MP (@lem7990847 A N y) (@lem7990839 A N y h1)). Qed.
Lemma lem7990850 {A N : Type'} (a : cart A N) : ((term126 A N a) = a) = ((term126 A N a) = a).
Proof. exact (eq_refl ((term126 A N a) = a)). Qed.
Lemma lem7990851 {A N : Type'} : (term127 A N) = (term127 A N).
Proof. exact (fun_ext (fun a : cart A N => @lem7990850 A N a)). Qed.
Lemma lem7990852 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem7990854 {A N : Type'} : (term128 A N) = (term128 A N).
Proof. exact (MK_COMB (@lem7990852 A N) (@lem7990851 A N)). Qed.
Lemma lem7990855 {A N : Type'} (h1 : term122 A N) : term128 A N.
Proof. exact (EQ_MP (@lem7990854 A N) (@lem7990841 A N h1)). Qed.
Lemma lem7990863 {A N : Type'} (_105400 : type35 A N) (y : cart A N) (h1 : term242 A N y) : term251 A N y _105400.
Proof. exact (@lem7990848 A N y h1 _105400). Qed.
Lemma lem7990864 {A N : Type'} (_105400 : type35 A N) (y : cart A N) : (term251 A N y _105400) = (term239 A N _105400 y).
Proof. exact (eq_refl (term251 A N y _105400)). Qed.
Lemma lem7990866 {A N : Type'} (_105401 : cart A N) (h1 : term122 A N) : term252 A N _105401.
Proof. exact (@lem7990855 A N h1 _105401). Qed.
Lemma lem7990867 {A N : Type'} (_105401 : cart A N) : (term252 A N _105401) = ((term126 A N _105401) = _105401).
Proof. exact (eq_refl (term252 A N _105401)). Qed.
Lemma lem7990873 {A N : Type'} (_105400 : type35 A N) (y : cart A N) (h1 : term242 A N y) : term239 A N _105400 y.
Proof. exact (EQ_MP (@lem7990864 A N _105400 y) (@lem7990863 A N _105400 y h1)). Qed.
Lemma lem7990899 {A N : Type'} (_105401 : cart A N) (h1 : term122 A N) : (term126 A N _105401) = _105401.
Proof. exact (EQ_MP (@lem7990867 A N _105401) (@lem7990866 A N _105401 h1)). Qed.
Lemma lem7990900 {A N : Type'} (_105401 : cart A N) (h1 : term122 A N) : (term126 A N _105401) = _105401.
Proof. exact (@lem7990899 A N _105401 h1). Qed.
Lemma lem7990901 {A N : Type'} (y : cart A N) (h1 : term122 A N) : (term126 A N y) = y.
Proof. exact (@lem7990900 A N y h1). Qed.
Lemma lem7990902 {A N : Type'} (y : cart A N) (h1 : term122 A N) : term253 A N y.
Proof. exact (fun h0 : term254 A N y => @lem7990901 A N y h1). Qed.
Lemma lem7990904 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7990905 {A N : Type'} (y : cart A N) : (term253 A N y) = ((term126 A N y) = y).
Proof. exact (@lem7990904 ((term126 A N y) = y)). Qed.
Lemma lem7990906 {A N : Type'} (y : cart A N) (h1 : term122 A N) : (term126 A N y) = y.
Proof. exact (EQ_MP (@lem7990905 A N y) (@lem7990902 A N y h1)). Qed.
Lemma lem7990909 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7990911 {A N : Type'} (_105400 : type35 A N) (y : cart A N) : (term239 A N _105400 y) = (term255 A N _105400 y).
Proof. exact (@lem7990909 ((@mk_cart A N _105400) = y)). Qed.
Lemma lem7990914 {A N : Type'} (_105400 : type35 A N) (y : cart A N) (h1 : term242 A N y) : term255 A N _105400 y.
Proof. exact (EQ_MP (@lem7990911 A N _105400 y) (@lem7990873 A N _105400 y h1)). Qed.
Lemma lem7990915 {A N : Type'} (_105400 : type35 A N) (y : cart A N) (h1 : term242 A N y) : term255 A N _105400 y.
Proof. exact (@lem7990914 A N _105400 y h1). Qed.
Lemma lem7990916 {A N : Type'} (y : cart A N) (h1 : term242 A N y) : term256 A N y.
Proof. exact (@lem7990915 A N (@dest_cart A N y) y h1). Qed.
Lemma lem7990919 {A N : Type'} (y : cart A N) (h1 : term242 A N y) (h2 : term122 A N) : False.
Proof. exact (@lem7990916 A N y h1 (@lem7990906 A N y h2)). Qed.
Lemma lem7990920 {A N : Type'} (y : cart A N) (h1 : term242 A N y) (h2 : term122 A N) : term199.
Proof. exact (fun h0 : ~ False => @lem7990919 A N y h1 h2). Qed.
Lemma lem7990922 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7990923 : term199 = False.
Proof. exact (@lem7990922 False). Qed.
Lemma lem7990924 {A N : Type'} (y : cart A N) (h1 : term242 A N y) (h2 : term122 A N) : False.
Proof. exact (EQ_MP (@lem7990923) (@lem7990920 A N y h1 h2)). Qed.
Lemma lem7990925 {A N : Type'} (y : cart A N) (h1 : term242 A N y) (h2 : term122 A N) : (term242 A N y) = False.
Proof. exact (prop_ext (fun h3 : term242 A N y => @lem7990924 A N y h1 h2) (fun h3 : False => @lem7990848 A N y h1)). Qed.
Lemma lem7990926 {A N : Type'} (y : cart A N) (h1 : term242 A N y) (h2 : term122 A N) : False.
Proof. exact (EQ_MP (@lem7990925 A N y h1 h2) (@lem7990848 A N y h1)). Qed.
Lemma lem7990927 {A N : Type'} (y : cart A N) (h1 : term242 A N y) (h2 : term122 A N) : (term242 A N y) = False.
Proof. exact (prop_ext (fun h3 : term242 A N y => @lem7990926 A N y h1 h2) (fun h3 : False => @lem7990839 A N y h1)). Qed.
Lemma lem7990928 {A N : Type'} (y : cart A N) (h1 : term242 A N y) (h2 : term122 A N) : False.
Proof. exact (EQ_MP (@lem7990927 A N y h1 h2) (@lem7990839 A N y h1)). Qed.
Lemma lem7990929 {A N : Type'} (y : cart A N) (h1 : term242 A N y) (h2 : term122 A N) : (term122 A N) = False.
Proof. exact (prop_ext (fun h3 : term122 A N => @lem7990928 A N y h1 h2) (fun h3 : False => @lem7990826 A N h2)). Qed.
Lemma lem7990930 {A N : Type'} (y : cart A N) (h1 : term242 A N y) (h2 : term122 A N) : False.
Proof. exact (EQ_MP (@lem7990929 A N y h1 h2) (@lem7990826 A N h2)). Qed.
Lemma lem7990931 {A N : Type'} (h1 : term225 A N) (h2 : term122 A N) : False.
Proof. exact (ex_elim (@lem7990773 A N h1) (fun y : cart A N => fun h0 : term249 A N y => @lem7990930 A N y h0 h2)). Qed.
Lemma lem7990932 {A N : Type'} (h1 : term225 A N) (h2 : term122 A N) : (term122 A N) = False.
Proof. exact (prop_ext (fun h3 : term122 A N => @lem7990931 A N h1 h2) (fun h3 : False => @lem7990797 A N h2)). Qed.
Lemma lem7990933 {A N : Type'} (h1 : term225 A N) (h2 : term122 A N) : False.
Proof. exact (EQ_MP (@lem7990932 A N h1 h2) (@lem7990797 A N h2)). Qed.
Lemma lem7990934 {A N : Type'} (h1 : term225 A N) : term200 A N.
Proof. exact (fun h0 : term122 A N => @lem7990933 A N h1 h0). Qed.
Lemma lem7990935 {A N : Type'} : (term200 A N) = (term123 A N).
Proof. exact (@lem69 (term122 A N)). Qed.
Lemma lem7990936 {A N : Type'} (h1 : term225 A N) : term123 A N.
Proof. exact (EQ_MP (@lem7990935 A N) (@lem7990934 A N h1)). Qed.
Lemma lem7990937 {A N : Type'} : term231 A N.
Proof. exact (fun h0 : term225 A N => @lem7990936 A N h0). Qed.
Lemma lem7990938 {A N : Type'} : term226 A N.
Proof. exact (EQ_MP (@lem7990737 A N) (@lem7990937 A N)). Qed.
Lemma lem7990940 {A N : Type'} : term226 A N.
Proof. exact (@lem7990632 A N (@lem7990938 A N)). Qed.
Lemma lem7990941 {A N : Type'} (h1 : term225 A N) : term114 A N.
Proof. exact (@lem7990940 A N (@lem7990614 A N h1)). Qed.
Lemma lem7990942 {A N : Type'} (h1 : term225 A N) : False.
Proof. exact (@lem7990941 A N h1 (@lem7990615 A N)). Qed.
Lemma lem7990943 {A N : Type'} (h1 : term225 A N) : (term225 A N) = False.
Proof. exact (prop_ext (fun h2 : term225 A N => @lem7990942 A N h1) (fun h2 : False => @lem7990614 A N h1)). Qed.
Lemma lem7990944 {A N : Type'} (h1 : term225 A N) : False.
Proof. exact (EQ_MP (@lem7990943 A N h1) (@lem7990614 A N h1)). Qed.
Lemma lem7990945 {A N : Type'} : term224 A N.
Proof. exact (fun h0 : term225 A N => @lem7990944 A N h0). Qed.
Lemma lem7990946 {A N : Type'} : term211 A N.
Proof. exact (EQ_MP (@lem7990613 A N) (@lem7990945 A N)). Qed.
Lemma lem7990947 {A N : Type'} : term222 A N.
Proof. exact (EQ_MP (@lem7990609 A N) (@lem7990946 A N)). Qed.
Lemma lem7990948 {A N : Type'} : (@IMAGE ((finite_image N) -> A) (cart A N) (@mk_cart A N) (@UNIV ((finite_image N) -> A))) = (@UNIV (cart A N)).
Proof. exact (@lem7990524 A N (@lem7990947 A N)). Qed.
Lemma lem7990949 {A N : Type'} : (term257 A N) = (@HAS_SIZE (cart A N) (@UNIV (cart A N))).
Proof. exact (MK_COMB (@lem7990520 A N) (@lem7990948 A N)). Qed.
Lemma lem7990950 {A N : Type'} (m : nat) : (term97 A N m) = (term101 A N m).
Proof. exact (MK_COMB (@lem7990949 A N) (@lem7990519 N m)). Qed.
Lemma lem7990951 {A N : Type'} (m : nat) : term258 A N m.
Proof. exact (@lem7990518 A N m (@lem7990950 A N m)). Qed.
Lemma lem7990952 {A N : Type'} (m : nat) : term259 A N m.
Proof. exact (conj (@lem7990515 A N) (@lem7990951 A N m)). Qed.
Lemma lem7990953 {A N : Type'} (m : nat) : term103 A N m.
Proof. exact (@lem7989897 A N m (@lem7990952 A N m)). Qed.
Lemma lem7990954 {A N : Type'} (m : nat) : term102 A N m.
Proof. exact (EQ_MP (@lem7989894 A N m) (@lem7990953 A N m)). Qed.
Lemma lem7990955 {A N : Type'} (m : nat) (h1 : term58 A N m) : term101 A N m.
Proof. exact (@lem7990954 A N m (@lem7989811 A N m h1)). Qed.
Lemma lem7990956 {A N : Type'} (m : nat) : term260 A N m.
Proof. exact (fun h0 : term58 A N m => @lem7990955 A N m h0). Qed.
Lemma lem7990957 {A N : Type'} (m : nat) (h1 : term58 A N m) : term101 A N m.
Proof. exact (@lem7990956 A N m (@lem7989755 A N m h1)). Qed.
Lemma lem7990958 {A N : Type'} (m : nat) (h1 : @HAS_SIZE A (@UNIV A) m) : (term58 A N m) = (term101 A N m).
Proof. exact (prop_ext (fun h2 : term58 A N m => @lem7990957 A N m h2) (fun h2 : term101 A N m => @lem7989801 A N m h1)). Qed.
Lemma lem7990959 {A N : Type'} (m : nat) (h1 : @HAS_SIZE A (@UNIV A) m) : term101 A N m.
Proof. exact (EQ_MP (@lem7990958 A N m h1) (@lem7989801 A N m h1)). Qed.
Lemma lem7990960 {A N : Type'} (m : nat) (h1 : @HAS_SIZE A (@UNIV A) m) : (@HAS_SIZE A (@UNIV A) m) = (term101 A N m).
Proof. exact (prop_ext (fun h2 : @HAS_SIZE A (@UNIV A) m => @lem7990959 A N m h1) (fun h2 : term101 A N m => @lem7989754 A m h1)). Qed.
Lemma lem7990961 {A N : Type'} (m : nat) (h1 : @HAS_SIZE A (@UNIV A) m) : term101 A N m.
Proof. exact (EQ_MP (@lem7990960 A N m h1) (@lem7989754 A m h1)). Qed.
Lemma lem7990962 {A N : Type'} (m : nat) : term261 A N m.
Proof. exact (fun h0 : @HAS_SIZE A (@UNIV A) m => @lem7990961 A N m h0). Qed.
Lemma lem7990967 {A N : Type'} : term262 A N.
Proof. exact (fun m : nat => @lem7990962 A N m). Qed.
