Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_DIV_POW2_ALT_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_LE_spec.
Require Import REAL_DIV_POW2_spec.
Require Import REAL_INV_DIV_spec.
Require Import REAL_INV_INV_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1641481 (m : nat) (n : nat) : term0 m n.
Proof. exact (@lem9784 (Peano.le m n)). Qed.
Lemma lem1641482 (m : nat) (n : nat) : (term0 m n) = (term1 m n).
Proof. exact (eq_refl (term0 m n)). Qed.
Lemma lem1641483 (m : nat) (n : nat) : term1 m n.
Proof. exact (EQ_MP (@lem1641482 m n) (@lem1641481 m n)). Qed.
Lemma lem1641484 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1641485 (m : nat) (n : nat) (h1 : term2 m n) : term2 m n.
Proof. exact (h1). Qed.
Lemma lem1641488 (n : nat) (m : nat) (h1 : (term2 m n) = (Peano.lt n m)) : (term2 m n) = (Peano.lt n m).
Proof. exact (h1). Qed.
Lemma lem1641489 (n : nat) (m : nat) (h1 : (term2 m n) = (Peano.lt n m)) : (Peano.lt n m) = (term2 m n).
Proof. exact (SYM (@lem1641488 n m h1)). Qed.
Lemma lem1641490 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term2 m n)) : (Peano.lt n m) = (term2 m n).
Proof. exact (h1). Qed.
Lemma lem1641491 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term2 m n)) : (term2 m n) = (Peano.lt n m).
Proof. exact (SYM (@lem1641490 m n h1)). Qed.
Lemma lem1641492 (m : nat) (n : nat) : ((term2 m n) = (Peano.lt n m)) = ((Peano.lt n m) = (term2 m n)).
Proof. exact (prop_ext (fun h1 : (term2 m n) = (Peano.lt n m) => @lem1641489 n m h1) (fun h1 : (Peano.lt n m) = (term2 m n) => @lem1641491 m n h1)). Qed.
Lemma lem1641493 (m : nat) : (term3 m) = (term4 m).
Proof. exact (fun_ext (fun n : nat => @lem1641492 m n)). Qed.
Lemma lem1641494 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1641495 (m : nat) : (term5 m) = (term6 m).
Proof. exact (MK_COMB (@lem1641494) (@lem1641493 m)). Qed.
Lemma lem1641496 : term7 = term8.
Proof. exact (fun_ext (fun m : nat => @lem1641495 m)). Qed.
Lemma lem1641497 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1641498 : term9 = term10.
Proof. exact (MK_COMB (@lem1641497) (@lem1641496)). Qed.
Lemma lem1641499 : term10.
Proof. exact (EQ_MP (@lem1641498) (@lem97961)). Qed.
Lemma lem1641500 (x : real) : term11 x.
Proof. exact (@lem1595376 x). Qed.
Lemma lem1641501 (x : real) : (term11 x) = (term12 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1641502 (x : real) : term12 x.
Proof. exact (EQ_MP (@lem1641501 x) (@lem1641500 x)). Qed.
Lemma lem1641503 (x : real) (y : real) : term13 x y.
Proof. exact (@lem1641502 x y). Qed.
Lemma lem1641504 (y : real) (x : real) : (term13 x y) = ((term14 x y) = (real_div y x)).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1641507 (x : real) (h1 : (term15 x) = x) : (term15 x) = x.
Proof. exact (h1). Qed.
Lemma lem1641508 (x : real) (h1 : (term15 x) = x) : x = (term15 x).
Proof. exact (SYM (@lem1641507 x h1)). Qed.
Lemma lem1641509 (x : real) (h1 : x = (term15 x)) : x = (term15 x).
Proof. exact (h1). Qed.
Lemma lem1641510 (x : real) (h1 : x = (term15 x)) : (term15 x) = x.
Proof. exact (SYM (@lem1641509 x h1)). Qed.
Lemma lem1641511 (x : real) : ((term15 x) = x) = (x = (term15 x)).
Proof. exact (prop_ext (fun h1 : (term15 x) = x => @lem1641508 x h1) (fun h1 : x = (term15 x) => @lem1641510 x h1)). Qed.
Lemma lem1641512 : term16 = term17.
Proof. exact (fun_ext (fun x : real => @lem1641511 x)). Qed.
Lemma lem1641513 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1641514 : term18 = term19.
Proof. exact (MK_COMB (@lem1641513) (@lem1641512)). Qed.
Lemma lem1641515 : term19.
Proof. exact (EQ_MP (@lem1641514) (@lem1587920)). Qed.
Lemma lem1641516 (x : real) : term20 x.
Proof. exact (@lem1641515 x). Qed.
Lemma lem1641517 (x : real) : (term20 x) = (x = (term15 x)).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1641519 (x : real) (h1 : term21 x) : term21 x.
Proof. exact (h1). Qed.
Lemma lem1641521 (x : real) : x = (term15 x).
Proof. exact (EQ_MP (@lem1641517 x) (@lem1641516 x)). Qed.
Lemma lem1641522 (m : nat) (x : real) (n : nat) : (term22 m x n) = (term23 m x n).
Proof. exact (@lem1641521 (term22 m x n)). Qed.
Lemma lem1641523 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1641524 (m : nat) (x : real) (n : nat) : (term24 m x n) = (term25 m x n).
Proof. exact (MK_COMB (@lem1641523) (@lem1641522 m x n)). Qed.
Lemma lem1641525 (x : real) (n : nat) (m : nat) : (term26 x n m) = (term26 x n m).
Proof. exact (eq_refl (term26 x n m)). Qed.
Lemma lem1641526 (x : real) (n : nat) (m : nat) : ((term22 m x n) = (term26 x n m)) = ((term23 m x n) = (term26 x n m)).
Proof. exact (MK_COMB (@lem1641524 m x n) (@lem1641525 x n m)). Qed.
Lemma lem1641527 (x : real) (n : nat) (m : nat) : ((term23 m x n) = (term26 x n m)) = ((term22 m x n) = (term26 x n m)).
Proof. exact (SYM (@lem1641526 x n m)). Qed.
Lemma lem1641531 (y : real) (x : real) : (term14 x y) = (real_div y x).
Proof. exact (EQ_MP (@lem1641504 y x) (@lem1641503 x y)). Qed.
Lemma lem1641532 (n : nat) (x : real) (m : nat) : (term27 m x n) = (term22 n x m).
Proof. exact (@lem1641531 (real_pow x n) (real_pow x m)). Qed.
Lemma lem1641533 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1641534 (n : nat) (x : real) (m : nat) : (term23 m x n) = (term27 n x m).
Proof. exact (MK_COMB (@lem1641533) (@lem1641532 n x m)). Qed.
Lemma lem1641535 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1641536 (n : nat) (x : real) (m : nat) : (term25 m x n) = (term28 n x m).
Proof. exact (MK_COMB (@lem1641535) (@lem1641534 n x m)). Qed.
Lemma lem1641537 (x : real) (n : nat) (m : nat) : (term26 x n m) = (term26 x n m).
Proof. exact (eq_refl (term26 x n m)). Qed.
Lemma lem1641538 (x : real) (n : nat) (m : nat) : ((term23 m x n) = (term26 x n m)) = ((term27 n x m) = (term26 x n m)).
Proof. exact (MK_COMB (@lem1641536 n x m) (@lem1641537 x n m)). Qed.
Lemma lem1641539 (x : real) (n : nat) (m : nat) : ((term27 n x m) = (term26 x n m)) = ((term23 m x n) = (term26 x n m)).
Proof. exact (SYM (@lem1641538 x n m)). Qed.
Lemma lem1641540 (x : real) : term29 x.
Proof. exact (@lem1641480 x). Qed.
Lemma lem1641541 (x : real) : (term29 x) = (term30 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1641542 (x : real) : term30 x.
Proof. exact (EQ_MP (@lem1641541 x) (@lem1641540 x)). Qed.
Lemma lem1641543 (x : real) (m : nat) : term31 x m.
Proof. exact (@lem1641542 x m). Qed.
Lemma lem1641544 (x : real) (m : nat) : (term31 x m) = (term32 x m).
Proof. exact (eq_refl (term31 x m)). Qed.
Lemma lem1641545 (x : real) (m : nat) : term32 x m.
Proof. exact (EQ_MP (@lem1641544 x m) (@lem1641543 x m)). Qed.
Lemma lem1641546 (x : real) (m : nat) (n : nat) : term33 x m n.
Proof. exact (@lem1641545 x m n). Qed.
Lemma lem1641547 (x : real) (n : nat) (m : nat) : (term33 x m n) = (term34 x n m).
Proof. exact (eq_refl (term33 x m n)). Qed.
Lemma lem1641548 (x : real) (n : nat) (m : nat) : term34 x n m.
Proof. exact (EQ_MP (@lem1641547 x n m) (@lem1641546 x m n)). Qed.
Lemma lem1641549 (x : real) (h1 : term21 x) : term21 x.
Proof. exact (h1). Qed.
Lemma lem1641550 (n : nat) (m : nat) (x : real) (h1 : term21 x) : (term22 m x n) = (term35 x n m).
Proof. exact (@lem1641548 x n m (@lem1641549 x h1)). Qed.
Lemma lem1641556 (m : nat) : term36 m.
Proof. exact (@lem1641499 m). Qed.
Lemma lem1641557 (m : nat) : (term36 m) = (term6 m).
Proof. exact (eq_refl (term36 m)). Qed.
Lemma lem1641558 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem1641557 m) (@lem1641556 m)). Qed.
Lemma lem1641559 (m : nat) (n : nat) : term37 m n.
Proof. exact (@lem1641558 m n). Qed.
Lemma lem1641560 (m : nat) (n : nat) : (term37 m n) = ((Peano.lt n m) = (term2 m n)).
Proof. exact (eq_refl (term37 m n)). Qed.
Lemma lem1641562 (x : real) : term38 x.
Proof. exact (@lem82 (x = term39)). Qed.
Lemma lem1641578 (x : real) (n : nat) (m : nat) : term34 x n m.
Proof. exact (fun h0 : term21 x => @lem1641550 n m x h0). Qed.
Lemma lem1641579 (x : real) (m : nat) (n : nat) : term34 x m n.
Proof. exact (@lem1641578 x m n). Qed.
Lemma lem1641581 (x : real) (h1 : term21 x) : (x = term39) = False.
Proof. exact (@lem1641562 x (@lem1641519 x h1)). Qed.
Lemma lem1641582 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1641583 (x : real) (h1 : term21 x) : (term21 x) = (~ False).
Proof. exact (MK_COMB (@lem1641582) (@lem1641581 x h1)). Qed.
Lemma lem1641585 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1641586 (x : real) (h1 : term21 x) : (term21 x) = True.
Proof. exact (TRANS (@lem1641583 x h1) (@lem1641585)). Qed.
Lemma lem1641587 (x : real) (h1 : term21 x) : True = (term21 x).
Proof. exact (SYM (@lem1641586 x h1)). Qed.
Lemma lem1641588 (x : real) (h1 : term21 x) : term21 x.
Proof. exact (EQ_MP (@lem1641587 x h1) (@lem0)). Qed.
Lemma lem1641589 (m : nat) (n : nat) (x : real) (h1 : term21 x) : (term22 n x m) = (term35 x m n).
Proof. exact (@lem1641579 x m n (@lem1641588 x h1)). Qed.
Lemma lem1641623 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1641624 (m : nat) (n : nat) (x : real) (h1 : term21 x) : (term27 n x m) = (term40 x m n).
Proof. exact (MK_COMB (@lem1641623) (@lem1641589 m n x h1)). Qed.
Lemma lem1641658 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1641659 (m : nat) (n : nat) (x : real) (h1 : term21 x) : (term28 n x m) = (term41 x m n).
Proof. exact (MK_COMB (@lem1641658) (@lem1641624 m n x h1)). Qed.
Lemma lem1641694 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term42 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem1641695 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term43 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem1641694 _2963 g t e g' t' e'). Qed.
Lemma lem1641696 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term44 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem1641695 _2963 g t e g' t'). Qed.
Lemma lem1641697 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term45 _2963 g t e.
Proof. exact (fun g' : Prop => @lem1641696 _2963 g t e g'). Qed.
Lemma lem1641698 (g : Prop) (t : real) (e : real) : term46 g t e.
Proof. exact (@lem1641697 real g t e). Qed.
Lemma lem1641699 (x : real) (n : nat) (m : nat) : term47 x n m.
Proof. exact (@lem1641698 (Peano.lt n m) (term48 x m n) (term49 x n m)). Qed.
Lemma lem1641700 (x : real) (n : nat) (m : nat) (g' : Prop) : term50 x n m g'.
Proof. exact (@lem1641699 x n m g'). Qed.
Lemma lem1641701 (x : real) (n : nat) (m : nat) (g' : Prop) : (term50 x n m g') = (term51 x n m g').
Proof. exact (eq_refl (term50 x n m g')). Qed.
Lemma lem1641702 (x : real) (n : nat) (m : nat) (g' : Prop) : term51 x n m g'.
Proof. exact (EQ_MP (@lem1641701 x n m g') (@lem1641700 x n m g')). Qed.
Lemma lem1641703 (x : real) (n : nat) (m : nat) (g' : Prop) (t' : real) : term52 x n m g' t'.
Proof. exact (@lem1641702 x n m g' t'). Qed.
Lemma lem1641704 (x : real) (n : nat) (m : nat) (g' : Prop) (t' : real) : (term52 x n m g' t') = (term53 x n m g' t').
Proof. exact (eq_refl (term52 x n m g' t')). Qed.
Lemma lem1641705 (x : real) (n : nat) (m : nat) (g' : Prop) (t' : real) : term53 x n m g' t'.
Proof. exact (EQ_MP (@lem1641704 x n m g' t') (@lem1641703 x n m g' t')). Qed.
Lemma lem1641706 (x : real) (n : nat) (m : nat) (g' : Prop) (t' : real) (e' : real) : term54 x n m g' t' e'.
Proof. exact (@lem1641705 x n m g' t' e'). Qed.
Lemma lem1641707 (x : real) (n : nat) (m : nat) (g' : Prop) (t' : real) (e' : real) : (term54 x n m g' t' e') = (term55 x n m g' t' e').
Proof. exact (eq_refl (term54 x n m g' t' e')). Qed.
Lemma lem1641708 (x : real) (n : nat) (m : nat) (g' : Prop) (t' : real) (e' : real) : term55 x n m g' t' e'.
Proof. exact (EQ_MP (@lem1641707 x n m g' t' e') (@lem1641706 x n m g' t' e')). Qed.
Lemma lem1641710 (m : nat) (n : nat) : (Peano.lt n m) = (term2 m n).
Proof. exact (EQ_MP (@lem1641560 m n) (@lem1641559 m n)). Qed.
Lemma lem1641711 (x : real) (m : nat) (n : nat) (t' : real) (e' : real) : term56 x m n t' e'.
Proof. exact (@lem1641708 x n m (term2 m n) t' e'). Qed.
Lemma lem1641712 (x : real) (m : nat) (n : nat) (t' : real) (e' : real) : term57 x m n t' e'.
Proof. exact (@lem1641711 x m n t' e' (@lem1641710 m n)). Qed.
Lemma lem1641716 (x : real) (m : nat) (n : nat) : (term48 x m n) = (term48 x m n).
Proof. exact (eq_refl (term48 x m n)). Qed.
Lemma lem1641717 (x : real) (m : nat) (n : nat) : term58 x m n.
Proof. exact (fun h0 : term2 m n => @lem1641716 x m n). Qed.
Lemma lem1641718 (x : real) (m : nat) (n : nat) (e' : real) : term59 x m n e'.
Proof. exact (@lem1641712 x m n (term48 x m n) e'). Qed.
Lemma lem1641719 (x : real) (m : nat) (n : nat) (e' : real) : term60 x m n e'.
Proof. exact (@lem1641718 x m n e' (@lem1641717 x m n)). Qed.
Lemma lem1641723 (x : real) (n : nat) (m : nat) : (term49 x n m) = (term49 x n m).
Proof. exact (eq_refl (term49 x n m)). Qed.
Lemma lem1641724 (x : real) (n : nat) (m : nat) : term61 x n m.
Proof. exact (fun h0 : term62 m n => @lem1641723 x n m). Qed.
Lemma lem1641725 (x : real) (n : nat) (m : nat) : term63 x n m.
Proof. exact (@lem1641719 x m n (term49 x n m)). Qed.
Lemma lem1641726 (x : real) (n : nat) (m : nat) : (term26 x n m) = (term64 x n m).
Proof. exact (@lem1641725 x n m (@lem1641724 x n m)). Qed.
Lemma lem1641760 (n : nat) (m : nat) (x : real) (h1 : term21 x) : ((term27 n x m) = (term26 x n m)) = ((term40 x m n) = (term64 x n m)).
Proof. exact (MK_COMB (@lem1641659 m n x h1) (@lem1641726 x n m)). Qed.
Lemma lem1641829 (n : nat) (m : nat) (x : real) (h1 : term21 x) : ((term40 x m n) = (term64 x n m)) = ((term27 n x m) = (term26 x n m)).
Proof. exact (SYM (@lem1641760 n m x h1)). Qed.
Lemma lem1641846 (m : nat) (n : nat) : (Peano.le m n) = ((Peano.le m n) = True).
Proof. exact (@lem7 (Peano.le m n)). Qed.
Lemma lem1641851 (m : nat) (n : nat) (h1 : Peano.le m n) : (Peano.le m n) = True.
Proof. exact (EQ_MP (@lem1641846 m n) (@lem1641484 m n h1)). Qed.
Lemma lem1641852 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1641853 (m : nat) (n : nat) (h1 : Peano.le m n) : (term65 m n) = (@COND real True).
Proof. exact (MK_COMB (@lem1641852) (@lem1641851 m n h1)). Qed.
Lemma lem1641854 (x : real) (n : nat) (m : nat) : (term48 x n m) = (term48 x n m).
Proof. exact (eq_refl (term48 x n m)). Qed.
Lemma lem1641855 (x : real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term66 x n m) = (term67 x n m).
Proof. exact (MK_COMB (@lem1641853 m n h1) (@lem1641854 x n m)). Qed.
Lemma lem1641856 (x : real) (m : nat) (n : nat) : (term49 x m n) = (term49 x m n).
Proof. exact (eq_refl (term49 x m n)). Qed.
Lemma lem1641857 (x : real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term35 x m n) = (term68 x m n).
Proof. exact (MK_COMB (@lem1641855 x m n h1) (@lem1641856 x m n)). Qed.
Lemma lem1641859 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1641860 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1641859 real t2 t1). Qed.
Lemma lem1641861 (x : real) (n : nat) (m : nat) : (term68 x m n) = (term48 x n m).
Proof. exact (@lem1641860 (term49 x m n) (term48 x n m)). Qed.
Lemma lem1641862 (x : real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term35 x m n) = (term48 x n m).
Proof. exact (TRANS (@lem1641857 x m n h1) (@lem1641861 x n m)). Qed.
Lemma lem1641863 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1641864 (x : real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term40 x m n) = (term49 x n m).
Proof. exact (MK_COMB (@lem1641863) (@lem1641862 x m n h1)). Qed.
Lemma lem1641865 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1641866 (x : real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term41 x m n) = (term69 x n m).
Proof. exact (MK_COMB (@lem1641865) (@lem1641864 x m n h1)). Qed.
Lemma lem1641868 (m : nat) (n : nat) (h1 : Peano.le m n) : (Peano.le m n) = True.
Proof. exact (EQ_MP (@lem1641846 m n) (@lem1641484 m n h1)). Qed.
Lemma lem1641869 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1641870 (m : nat) (n : nat) (h1 : Peano.le m n) : (term2 m n) = (~ True).
Proof. exact (MK_COMB (@lem1641869) (@lem1641868 m n h1)). Qed.
Lemma lem1641872 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1641873 (m : nat) (n : nat) (h1 : Peano.le m n) : (term2 m n) = False.
Proof. exact (TRANS (@lem1641870 m n h1) (@lem1641872)). Qed.
Lemma lem1641874 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1641875 (m : nat) (n : nat) (h1 : Peano.le m n) : (term70 m n) = (@COND real False).
Proof. exact (MK_COMB (@lem1641874) (@lem1641873 m n h1)). Qed.
Lemma lem1641876 (x : real) (m : nat) (n : nat) : (term48 x m n) = (term48 x m n).
Proof. exact (eq_refl (term48 x m n)). Qed.
Lemma lem1641877 (x : real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term71 x m n) = (term72 x m n).
Proof. exact (MK_COMB (@lem1641875 m n h1) (@lem1641876 x m n)). Qed.
Lemma lem1641878 (x : real) (n : nat) (m : nat) : (term49 x n m) = (term49 x n m).
Proof. exact (eq_refl (term49 x n m)). Qed.
Lemma lem1641879 (x : real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term64 x n m) = (term73 x n m).
Proof. exact (MK_COMB (@lem1641877 x m n h1) (@lem1641878 x n m)). Qed.
Lemma lem1641881 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1641882 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1641881 real t1 t2). Qed.
Lemma lem1641883 (x : real) (n : nat) (m : nat) : (term73 x n m) = (term49 x n m).
Proof. exact (@lem1641882 (term48 x m n) (term49 x n m)). Qed.
Lemma lem1641884 (x : real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term64 x n m) = (term49 x n m).
Proof. exact (TRANS (@lem1641879 x m n h1) (@lem1641883 x n m)). Qed.
Lemma lem1641885 (x : real) (m : nat) (n : nat) (h1 : Peano.le m n) : ((term40 x m n) = (term64 x n m)) = ((term49 x n m) = (term49 x n m)).
Proof. exact (MK_COMB (@lem1641866 x m n h1) (@lem1641884 x m n h1)). Qed.
Lemma lem1641887 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1641888 (x : real) : (x = x) = True.
Proof. exact (@lem1641887 real x). Qed.
Lemma lem1641889 (x : real) (n : nat) (m : nat) : ((term49 x n m) = (term49 x n m)) = True.
Proof. exact (@lem1641888 (term49 x n m)). Qed.
Lemma lem1641890 (x : real) (m : nat) (n : nat) (h1 : Peano.le m n) : ((term40 x m n) = (term64 x n m)) = True.
Proof. exact (TRANS (@lem1641885 x m n h1) (@lem1641889 x n m)). Qed.
Lemma lem1641891 (x : real) (m : nat) (n : nat) (h1 : Peano.le m n) : True = ((term40 x m n) = (term64 x n m)).
Proof. exact (SYM (@lem1641890 x m n h1)). Qed.
Lemma lem1641892 (x : real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term40 x m n) = (term64 x n m).
Proof. exact (EQ_MP (@lem1641891 x m n h1) (@lem0)). Qed.
Lemma lem1641893 (x : real) : term74 x.
Proof. exact (@lem1587920 x). Qed.
Lemma lem1641894 (x : real) : (term74 x) = ((term15 x) = x).
Proof. exact (eq_refl (term74 x)). Qed.
Lemma lem1641909 (m : nat) (n : nat) : term75 m n.
Proof. exact (@lem82 (Peano.le m n)). Qed.
Lemma lem1641914 (m : nat) (n : nat) (h1 : term2 m n) : (Peano.le m n) = False.
Proof. exact (@lem1641909 m n (@lem1641485 m n h1)). Qed.
Lemma lem1641915 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1641916 (m : nat) (n : nat) (h1 : term2 m n) : (term65 m n) = (@COND real False).
Proof. exact (MK_COMB (@lem1641915) (@lem1641914 m n h1)). Qed.
Lemma lem1641917 (x : real) (n : nat) (m : nat) : (term48 x n m) = (term48 x n m).
Proof. exact (eq_refl (term48 x n m)). Qed.
Lemma lem1641918 (x : real) (m : nat) (n : nat) (h1 : term2 m n) : (term66 x n m) = (term72 x n m).
Proof. exact (MK_COMB (@lem1641916 m n h1) (@lem1641917 x n m)). Qed.
Lemma lem1641919 (x : real) (m : nat) (n : nat) : (term49 x m n) = (term49 x m n).
Proof. exact (eq_refl (term49 x m n)). Qed.
Lemma lem1641920 (x : real) (m : nat) (n : nat) (h1 : term2 m n) : (term35 x m n) = (term73 x m n).
Proof. exact (MK_COMB (@lem1641918 x m n h1) (@lem1641919 x m n)). Qed.
Lemma lem1641922 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1641923 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1641922 real t1 t2). Qed.
Lemma lem1641924 (x : real) (m : nat) (n : nat) : (term73 x m n) = (term49 x m n).
Proof. exact (@lem1641923 (term48 x n m) (term49 x m n)). Qed.
Lemma lem1641925 (x : real) (m : nat) (n : nat) (h1 : term2 m n) : (term35 x m n) = (term49 x m n).
Proof. exact (TRANS (@lem1641920 x m n h1) (@lem1641924 x m n)). Qed.
Lemma lem1641926 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1641927 (x : real) (m : nat) (n : nat) (h1 : term2 m n) : (term40 x m n) = (term76 x m n).
Proof. exact (MK_COMB (@lem1641926) (@lem1641925 x m n h1)). Qed.
Lemma lem1641929 (x : real) : (term15 x) = x.
Proof. exact (EQ_MP (@lem1641894 x) (@lem1641893 x)). Qed.
Lemma lem1641930 (x : real) (m : nat) (n : nat) : (term76 x m n) = (term48 x m n).
Proof. exact (@lem1641929 (term48 x m n)). Qed.
Lemma lem1641931 (x : real) (m : nat) (n : nat) (h1 : term2 m n) : (term40 x m n) = (term48 x m n).
Proof. exact (TRANS (@lem1641927 x m n h1) (@lem1641930 x m n)). Qed.
Lemma lem1641932 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1641933 (x : real) (m : nat) (n : nat) (h1 : term2 m n) : (term41 x m n) = (term77 x m n).
Proof. exact (MK_COMB (@lem1641932) (@lem1641931 x m n h1)). Qed.
Lemma lem1641935 (m : nat) (n : nat) (h1 : term2 m n) : (Peano.le m n) = False.
Proof. exact (@lem1641909 m n (@lem1641485 m n h1)). Qed.
Lemma lem1641936 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1641937 (m : nat) (n : nat) (h1 : term2 m n) : (term2 m n) = (~ False).
Proof. exact (MK_COMB (@lem1641936) (@lem1641935 m n h1)). Qed.
Lemma lem1641939 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1641940 (m : nat) (n : nat) (h1 : term2 m n) : (term2 m n) = True.
Proof. exact (TRANS (@lem1641937 m n h1) (@lem1641939)). Qed.
Lemma lem1641941 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1641942 (m : nat) (n : nat) (h1 : term2 m n) : (term70 m n) = (@COND real True).
Proof. exact (MK_COMB (@lem1641941) (@lem1641940 m n h1)). Qed.
Lemma lem1641943 (x : real) (m : nat) (n : nat) : (term48 x m n) = (term48 x m n).
Proof. exact (eq_refl (term48 x m n)). Qed.
Lemma lem1641944 (x : real) (m : nat) (n : nat) (h1 : term2 m n) : (term71 x m n) = (term67 x m n).
Proof. exact (MK_COMB (@lem1641942 m n h1) (@lem1641943 x m n)). Qed.
Lemma lem1641945 (x : real) (n : nat) (m : nat) : (term49 x n m) = (term49 x n m).
Proof. exact (eq_refl (term49 x n m)). Qed.
Lemma lem1641946 (x : real) (m : nat) (n : nat) (h1 : term2 m n) : (term64 x n m) = (term68 x n m).
Proof. exact (MK_COMB (@lem1641944 x m n h1) (@lem1641945 x n m)). Qed.
Lemma lem1641948 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1641949 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1641948 real t2 t1). Qed.
Lemma lem1641950 (x : real) (m : nat) (n : nat) : (term68 x n m) = (term48 x m n).
Proof. exact (@lem1641949 (term49 x n m) (term48 x m n)). Qed.
Lemma lem1641951 (x : real) (m : nat) (n : nat) (h1 : term2 m n) : (term64 x n m) = (term48 x m n).
Proof. exact (TRANS (@lem1641946 x m n h1) (@lem1641950 x m n)). Qed.
Lemma lem1641952 (x : real) (m : nat) (n : nat) (h1 : term2 m n) : ((term40 x m n) = (term64 x n m)) = ((term48 x m n) = (term48 x m n)).
Proof. exact (MK_COMB (@lem1641933 x m n h1) (@lem1641951 x m n h1)). Qed.
Lemma lem1641954 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1641955 (x : real) : (x = x) = True.
Proof. exact (@lem1641954 real x). Qed.
Lemma lem1641956 (x : real) (m : nat) (n : nat) : ((term48 x m n) = (term48 x m n)) = True.
Proof. exact (@lem1641955 (term48 x m n)). Qed.
Lemma lem1641957 (x : real) (m : nat) (n : nat) (h1 : term2 m n) : ((term40 x m n) = (term64 x n m)) = True.
Proof. exact (TRANS (@lem1641952 x m n h1) (@lem1641956 x m n)). Qed.
Lemma lem1641958 (x : real) (m : nat) (n : nat) (h1 : term2 m n) : True = ((term40 x m n) = (term64 x n m)).
Proof. exact (SYM (@lem1641957 x m n h1)). Qed.
Lemma lem1641959 (x : real) (m : nat) (n : nat) (h1 : term2 m n) : (term40 x m n) = (term64 x n m).
Proof. exact (EQ_MP (@lem1641958 x m n h1) (@lem0)). Qed.
Lemma lem1641960 (x : real) (n : nat) (m : nat) : (term40 x m n) = (term64 x n m).
Proof. exact (or_elim (@lem1641483 m n) (fun h0 : Peano.le m n => @lem1641892 x m n h0) (fun h0 : term2 m n => @lem1641959 x m n h0)). Qed.
Lemma lem1641961 (n : nat) (m : nat) (x : real) (h1 : term21 x) : (term27 n x m) = (term26 x n m).
Proof. exact (EQ_MP (@lem1641829 n m x h1) (@lem1641960 x n m)). Qed.
Lemma lem1641962 (n : nat) (m : nat) (x : real) (h1 : term21 x) : (term23 m x n) = (term26 x n m).
Proof. exact (EQ_MP (@lem1641539 x n m) (@lem1641961 n m x h1)). Qed.
Lemma lem1641963 (n : nat) (m : nat) (x : real) (h1 : term21 x) : (term22 m x n) = (term26 x n m).
Proof. exact (EQ_MP (@lem1641527 x n m) (@lem1641962 n m x h1)). Qed.
Lemma lem1641964 (n : nat) (m : nat) (x : real) (h1 : term21 x) : (term21 x) = ((term22 m x n) = (term26 x n m)).
Proof. exact (prop_ext (fun h2 : term21 x => @lem1641963 n m x h1) (fun h2 : (term22 m x n) = (term26 x n m) => @lem1641519 x h1)). Qed.
Lemma lem1641965 (n : nat) (m : nat) (x : real) (h1 : term21 x) : (term22 m x n) = (term26 x n m).
Proof. exact (EQ_MP (@lem1641964 n m x h1) (@lem1641519 x h1)). Qed.
Lemma lem1641966 (x : real) (n : nat) (m : nat) : term78 x n m.
Proof. exact (fun h0 : term21 x => @lem1641965 n m x h0). Qed.
Lemma lem1641971 (x : real) (m : nat) : term79 x m.
Proof. exact (fun n : nat => @lem1641966 x n m). Qed.
Lemma lem1641976 (x : real) : term80 x.
Proof. exact (fun m : nat => @lem1641971 x m). Qed.
Lemma lem1641981 : term81.
Proof. exact (fun x : real => @lem1641976 x). Qed.
