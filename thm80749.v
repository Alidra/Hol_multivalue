Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm80749_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import thm75635_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem80633 (mul' : type1606) (h1 : (term0 mul') = term1) : (term0 mul') = term1.
Proof. exact (h1). Qed.
Lemma lem80634 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem80635 (n : nat) (mul' : type1606) (h1 : (term0 mul') = term1) : (term2 mul' n) = (term3 n).
Proof. exact (MK_COMB (@lem80633 mul' h1) (@lem80634 n)). Qed.
Lemma lem80636 (n : nat) : (term3 n) = (NUMERAL 0).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem80637 (mul' : type1606) (n : nat) : (term4 mul' n) = (term4 mul' n).
Proof. exact (eq_refl (term4 mul' n)). Qed.
Lemma lem80638 (mul' : type1606) (n : nat) : ((term2 mul' n) = (term3 n)) = ((term2 mul' n) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem80637 mul' n) (@lem80636 n)). Qed.
Lemma lem80639 (n : nat) (mul' : type1606) (h1 : (term0 mul') = term1) : (term2 mul' n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem80638 mul' n) (@lem80635 n mul' h1)). Qed.
Lemma lem80640 (mul' : type1606) (h1 : (term0 mul') = term1) : term5 mul'.
Proof. exact (fun n : nat => @lem80639 n mul' h1). Qed.
Lemma lem80641 (mul' : type1606) (h1 : term6 mul') : term6 mul'.
Proof. exact (h1). Qed.
Lemma lem80642 (m : nat) (mul' : type1606) (h1 : term6 mul') : term7 mul' m.
Proof. exact (@lem80641 mul' h1 m). Qed.
Lemma lem80643 (mul' : type1606) (m : nat) : (term7 mul' m) = ((term8 mul' m) = (term9 mul' m)).
Proof. exact (eq_refl (term7 mul' m)). Qed.
Lemma lem80644 (m : nat) (mul' : type1606) (h1 : term6 mul') : (term8 mul' m) = (term9 mul' m).
Proof. exact (EQ_MP (@lem80643 mul' m) (@lem80642 m mul' h1)). Qed.
Lemma lem80645 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem80646 (m : nat) (n : nat) (mul' : type1606) (h1 : term6 mul') : (term10 mul' m n) = (term11 mul' m n).
Proof. exact (MK_COMB (@lem80644 m mul' h1) (@lem80645 n)). Qed.
Lemma lem80647 (mul' : type1606) (m : nat) (n : nat) : (term11 mul' m n) = (term12 mul' m n).
Proof. exact (eq_refl (term11 mul' m n)). Qed.
Lemma lem80648 (mul' : type1606) (m : nat) (n : nat) : (term13 mul' m n) = (term13 mul' m n).
Proof. exact (eq_refl (term13 mul' m n)). Qed.
Lemma lem80649 (mul' : type1606) (m : nat) (n : nat) : ((term10 mul' m n) = (term11 mul' m n)) = ((term10 mul' m n) = (term12 mul' m n)).
Proof. exact (MK_COMB (@lem80648 mul' m n) (@lem80647 mul' m n)). Qed.
Lemma lem80650 (m : nat) (n : nat) (mul' : type1606) (h1 : term6 mul') : (term10 mul' m n) = (term12 mul' m n).
Proof. exact (EQ_MP (@lem80649 mul' m n) (@lem80646 m n mul' h1)). Qed.
Lemma lem80651 (m : nat) (mul' : type1606) (h1 : term6 mul') : term14 mul' m.
Proof. exact (fun n : nat => @lem80650 m n mul' h1). Qed.
Lemma lem80652 (mul' : type1606) (h1 : term6 mul') : term15 mul'.
Proof. exact (fun m : nat => @lem80651 m mul' h1). Qed.
Lemma lem80653 (mul' : type1606) (h1 : term16 mul') : term16 mul'.
Proof. exact (h1). Qed.
Lemma lem80654 (mul' : type1606) (h1 : term16 mul') : term6 mul'.
Proof. exact (proj2 (@lem80653 mul' h1)). Qed.
Lemma lem80655 (mul' : type1606) (h1 : term16 mul') : (term0 mul') = term1.
Proof. exact (proj1 (@lem80653 mul' h1)). Qed.
Lemma lem80656 (mul' : type1606) (h1 : term16 mul') : ((term0 mul') = term1) = (term5 mul').
Proof. exact (prop_ext (fun h2 : (term0 mul') = term1 => @lem80640 mul' h2) (fun h2 : term5 mul' => @lem80655 mul' h1)). Qed.
Lemma lem80657 (mul' : type1606) (h1 : term16 mul') : term5 mul'.
Proof. exact (EQ_MP (@lem80656 mul' h1) (@lem80655 mul' h1)). Qed.
Lemma lem80658 (mul' : type1606) (h1 : term16 mul') : (term6 mul') = (term15 mul').
Proof. exact (prop_ext (fun h2 : term6 mul' => @lem80652 mul' h2) (fun h2 : term15 mul' => @lem80654 mul' h1)). Qed.
Lemma lem80659 (mul' : type1606) (h1 : term16 mul') : term15 mul'.
Proof. exact (EQ_MP (@lem80658 mul' h1) (@lem80654 mul' h1)). Qed.
Lemma lem80660 (mul' : type1606) (h1 : term16 mul') : term17 mul'.
Proof. exact (conj (@lem80657 mul' h1) (@lem80659 mul' h1)). Qed.
Lemma lem80661 {A : Type'} (e : A) : term18 A e.
Proof. exact (@lem75635 A e). Qed.
Lemma lem80662 {A : Type'} (e : A) : (term18 A e) = (term19 A e).
Proof. exact (eq_refl (term18 A e)). Qed.
Lemma lem80663 {A : Type'} (e : A) : term19 A e.
Proof. exact (EQ_MP (@lem80662 A e) (@lem80661 A e)). Qed.
Lemma lem80664 {A : Type'} (e : A) (f : type1423 A) : term20 A e f.
Proof. exact (@lem80663 A e f). Qed.
Lemma lem80665 {A : Type'} (e : A) (f : type1423 A) : (term20 A e f) = (term21 A e f).
Proof. exact (eq_refl (term20 A e f)). Qed.
Lemma lem80666 {A : Type'} (e : A) (f : type1423 A) : term21 A e f.
Proof. exact (EQ_MP (@lem80665 A e f) (@lem80664 A e f)). Qed.
Lemma lem80667 (e : nat -> nat) (f : type1000) : term22 e f.
Proof. exact (@lem80666 (nat -> nat) e f). Qed.
Lemma lem80668 : term23.
Proof. exact (@lem80667 term1 term24). Qed.
Lemma lem80669 (fn : type1606) (n : nat) : (term25 fn n) = (term26 fn n).
Proof. exact (eq_refl (term25 fn n)). Qed.
Lemma lem80670 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem80671 (fn : type1606) (n : nat) : (term27 fn n) = (term28 fn n).
Proof. exact (MK_COMB (@lem80669 fn n) (@lem80670 n)). Qed.
Lemma lem80672 (fn : type1606) (n : nat) : (term28 fn n) = (term9 fn n).
Proof. exact (eq_refl (term28 fn n)). Qed.
Lemma lem80673 (fn : type1606) (n : nat) : (term27 fn n) = (term9 fn n).
Proof. exact (TRANS (@lem80671 fn n) (@lem80672 fn n)). Qed.
Lemma lem80674 (fn : type1606) (n : nat) : (term29 fn n) = (term29 fn n).
Proof. exact (eq_refl (term29 fn n)). Qed.
Lemma lem80675 (fn : type1606) (n : nat) : ((term8 fn n) = (term27 fn n)) = ((term8 fn n) = (term9 fn n)).
Proof. exact (MK_COMB (@lem80674 fn n) (@lem80673 fn n)). Qed.
Lemma lem80676 (fn : type1606) : (term30 fn) = (term31 fn).
Proof. exact (fun_ext (fun n : nat => @lem80675 fn n)). Qed.
Lemma lem80677 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem80678 (fn : type1606) : (term32 fn) = (term6 fn).
Proof. exact (MK_COMB (@lem80677) (@lem80676 fn)). Qed.
Lemma lem80679 (fn : type1606) : (term33 fn) = (term33 fn).
Proof. exact (eq_refl (term33 fn)). Qed.
Lemma lem80680 (fn : type1606) : (term34 fn) = (term16 fn).
Proof. exact (MK_COMB (@lem80679 fn) (@lem80678 fn)). Qed.
Lemma lem80681 : term35 = term36.
Proof. exact (fun_ext (fun fn : type1606 => @lem80680 fn)). Qed.
Lemma lem80682 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem80683 : term23 = term37.
Proof. exact (MK_COMB (@lem80682) (@lem80681)). Qed.
Lemma lem80684 : term37.
Proof. exact (EQ_MP (@lem80683) (@lem80668)). Qed.
Lemma lem80685 (mul' : type1606) (h1 : term16 mul') : term16 mul'.
Proof. exact (h1). Qed.
Lemma lem80686 (mul' : type1606) (h1 : term16 mul') : term6 mul'.
Proof. exact (proj2 (@lem80685 mul' h1)). Qed.
Lemma lem80687 (mul' : type1606) (h1 : term16 mul') : (term0 mul') = term1.
Proof. exact (proj1 (@lem80685 mul' h1)). Qed.
Lemma lem80688 (mul' : type1606) (h1 : term16 mul') : term16 mul'.
Proof. exact (conj (@lem80687 mul' h1) (@lem80686 mul' h1)). Qed.
Lemma lem80689 (mul' : type1606) (h1 : term16 mul') : term37.
Proof. exact (ex_intro term36 mul' (@lem80688 mul' h1)). Qed.
Lemma lem80690 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem80691 (h1 : term37) : term37.
Proof. exact (ex_elim (@lem80690 h1) (fun mul' : type1606 => fun h0 : term36 mul' => @lem80689 mul' h0)). Qed.
Lemma lem80692 : term37 = term37.
Proof. exact (prop_ext (fun h1 : term37 => @lem80691 h1) (fun h1 : term37 => @lem80684)). Qed.
Lemma lem80693 : term37.
Proof. exact (EQ_MP (@lem80692) (@lem80684)). Qed.
Lemma lem80694 (mul' : type1606) (h1 : term16 mul') : term38.
Proof. exact (ex_intro term39 mul' (@lem80660 mul' h1)). Qed.
Lemma lem80695 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem80696 (h1 : term37) : term38.
Proof. exact (ex_elim (@lem80695 h1) (fun mul' : type1606 => fun h0 : term36 mul' => @lem80694 mul' h0)). Qed.
Lemma lem80697 : term37 = term38.
Proof. exact (prop_ext (fun h1 : term37 => @lem80696 h1) (fun h1 : term38 => @lem80693)). Qed.
Lemma lem80698 : term38.
Proof. exact (EQ_MP (@lem80697) (@lem80693)). Qed.
Lemma lem80701 (mul' : type1606) (h1 : term17 mul') : term17 mul'.
Proof. exact (h1). Qed.
Lemma lem80702 (mul' : type1606) (h1 : term17 mul') : term38.
Proof. exact (ex_intro term39 mul' (@lem80701 mul' h1)). Qed.
Lemma lem80703 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem80704 (h1 : term38) : term38.
Proof. exact (ex_elim (@lem80703 h1) (fun mul' : type1606 => fun h0 : term39 mul' => @lem80702 mul' h0)). Qed.
Lemma lem80705 : term38 = term38.
Proof. exact (prop_ext (fun h1 : term38 => @lem80704 h1) (fun h1 : term38 => @lem80698)). Qed.
Lemma lem80706 : term38.
Proof. exact (EQ_MP (@lem80705) (@lem80698)). Qed.
Lemma lem80707 : term40.
Proof. exact (fun _2186 : nat => @lem80706). Qed.
Lemma lem80708 {A B : Type'} (P : type1413 A B) : term41 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem80709 {A B : Type'} (P : type1413 A B) : (term41 A B P) = ((term42 A B P) = (term43 A B P)).
Proof. exact (eq_refl (term41 A B P)). Qed.
Lemma lem80712 {A B : Type'} (P : type1413 A B) : (term42 A B P) = (term43 A B P).
Proof. exact (EQ_MP (@lem80709 A B P) (@lem80708 A B P)). Qed.
Lemma lem80713 (P : type1581) : (term44 P) = (term45 P).
Proof. exact (@lem80712 nat type1606 P). Qed.
Lemma lem80714 : term46 = term47.
Proof. exact (@lem80713 term48). Qed.
Lemma lem80715 (_2186 : nat) : (term49 _2186) = term39.
Proof. exact (eq_refl (term49 _2186)). Qed.
Lemma lem80716 (mul' : type1606) : mul' = mul'.
Proof. exact (eq_refl mul'). Qed.
Lemma lem80717 (_2186 : nat) (mul' : type1606) : (term50 _2186 mul') = (term51 mul').
Proof. exact (MK_COMB (@lem80715 _2186) (@lem80716 mul')). Qed.
Lemma lem80718 (mul' : type1606) : (term51 mul') = (term17 mul').
Proof. exact (eq_refl (term51 mul')). Qed.
Lemma lem80719 (_2186 : nat) (mul' : type1606) : (term50 _2186 mul') = (term17 mul').
Proof. exact (TRANS (@lem80717 _2186 mul') (@lem80718 mul')). Qed.
Lemma lem80720 (_2186 : nat) : (term52 _2186) = term39.
Proof. exact (fun_ext (fun mul' : type1606 => @lem80719 _2186 mul')). Qed.
Lemma lem80721 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem80722 (_2186 : nat) : (term53 _2186) = term38.
Proof. exact (MK_COMB (@lem80721) (@lem80720 _2186)). Qed.
Lemma lem80723 : term54 = term55.
Proof. exact (fun_ext (fun _2186 : nat => @lem80722 _2186)). Qed.
Lemma lem80724 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem80725 : term46 = term40.
Proof. exact (MK_COMB (@lem80724) (@lem80723)). Qed.
Lemma lem80726 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem80727 : term56 = term57.
Proof. exact (MK_COMB (@lem80726) (@lem80725)). Qed.
Lemma lem80728 (_2186 : nat) : (term49 _2186) = term39.
Proof. exact (eq_refl (term49 _2186)). Qed.
Lemma lem80729 (mul' : type1602) (_2186 : nat) : (mul' _2186) = (mul' _2186).
Proof. exact (eq_refl (mul' _2186)). Qed.
Lemma lem80730 (mul' : type1602) (_2186 : nat) : (term58 mul' _2186) = (term59 mul' _2186).
Proof. exact (MK_COMB (@lem80728 _2186) (@lem80729 mul' _2186)). Qed.
Lemma lem80731 (mul' : type1602) (_2186 : nat) : (term59 mul' _2186) = (term60 mul' _2186).
Proof. exact (eq_refl (term59 mul' _2186)). Qed.
Lemma lem80732 (mul' : type1602) (_2186 : nat) : (term58 mul' _2186) = (term60 mul' _2186).
Proof. exact (TRANS (@lem80730 mul' _2186) (@lem80731 mul' _2186)). Qed.
Lemma lem80733 (mul' : type1602) : (term61 mul') = (term62 mul').
Proof. exact (fun_ext (fun _2186 : nat => @lem80732 mul' _2186)). Qed.
Lemma lem80734 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem80735 (mul' : type1602) : (term63 mul') = (term64 mul').
Proof. exact (MK_COMB (@lem80734) (@lem80733 mul')). Qed.
Lemma lem80736 : term65 = term66.
Proof. exact (fun_ext (fun mul' : type1602 => @lem80735 mul')). Qed.
Lemma lem80737 : (@ex (nat -> nat -> nat -> nat)) = (@ex (nat -> nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat -> nat))). Qed.
Lemma lem80738 : term47 = term67.
Proof. exact (MK_COMB (@lem80737) (@lem80736)). Qed.
Lemma lem80739 : (term46 = term47) = (term40 = term67).
Proof. exact (MK_COMB (@lem80727) (@lem80738)). Qed.
Lemma lem80740 : term40 = term67.
Proof. exact (EQ_MP (@lem80739) (@lem80714)). Qed.
Lemma lem80741 : term67.
Proof. exact (EQ_MP (@lem80740) (@lem80707)). Qed.
Lemma lem80743 {A : Type'} : (@ex A) = (term68 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem80744 : (@ex (nat -> nat -> nat -> nat)) = term69.
Proof. exact (@lem80743 type1602). Qed.
Lemma lem80745 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem80746 : term67 = term70.
Proof. exact (MK_COMB (@lem80744) (@lem80745)). Qed.
Lemma lem80747 : term70 = term71.
Proof. exact (eq_refl term70). Qed.
Lemma lem80748 : term67 = term71.
Proof. exact (TRANS (@lem80746) (@lem80747)). Qed.
Lemma lem80749 : term71.
Proof. exact (EQ_MP (@lem80748) (@lem80741)). Qed.
