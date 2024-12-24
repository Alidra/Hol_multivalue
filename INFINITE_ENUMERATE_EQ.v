Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INFINITE_ENUMERATE_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import INFINITE_ENUMERATE_spec.
Require Import INFINITE_IMAGE_spec.
Require Import IN_UNIV_spec.
Require Import LT_REFL_spec.
Require Import WLOG_LT_spec.
Require Import num_INFINITE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem4770669 (P : type1605) (h1 : term0 P) : term0 P.
Proof. exact (h1). Qed.
Lemma lem4770670 (P : type1605) (h1 : term1 P) : term1 P.
Proof. exact (h1). Qed.
Lemma lem4770671 (P : type1605) (h1 : term1 P) (h2 : term0 P) : term2 P.
Proof. exact (@lem4770669 P h2 (@lem4770670 P h1)). Qed.
Lemma lem4770672 (P : type1605) (h1 : term1 P) : term3 P.
Proof. exact (fun h0 : term0 P => @lem4770671 P h1 h0). Qed.
Lemma lem4770673 (P : type1605) (h1 : term0 P) : term0 P.
Proof. exact (h1). Qed.
Lemma lem4770674 (P : type1605) (h1 : term1 P) (h2 : term0 P) : term2 P.
Proof. exact (@lem4770672 P h1 (@lem4770673 P h2)). Qed.
Lemma lem4770675 (P : type1605) (h1 : term0 P) : term0 P.
Proof. exact (fun h0 : term1 P => @lem4770674 P h0 h1). Qed.
Lemma lem4770676 (P : type1605) : term4 P.
Proof. exact (fun h0 : term0 P => @lem4770675 P h0). Qed.
Lemma lem4770678 {A : Type'} (x : A) : term5 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem4770679 {A : Type'} (x : A) : (term5 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term5 A x)). Qed.
Lemma lem4770680 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem4770679 A x) (@lem4770678 A x)). Qed.
Lemma lem4770681 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem4770683 : (@INFINITE nat (@UNIV nat)) = ((@INFINITE nat (@UNIV nat)) = True).
Proof. exact (@lem7 (@INFINITE nat (@UNIV nat))). Qed.
Lemma lem4770685 {A B : Type'} (h1 : term6 A B) : term6 A B.
Proof. exact (h1). Qed.
Lemma lem4770686 {A B : Type'} (f : A -> B) (h1 : term6 A B) : term7 A B f.
Proof. exact (@lem4770685 A B h1 f). Qed.
Lemma lem4770687 {A B : Type'} (f : A -> B) : (term7 A B f) = (term8 A B f).
Proof. exact (eq_refl (term7 A B f)). Qed.
Lemma lem4770688 {A B : Type'} (f : A -> B) (h1 : term6 A B) : term8 A B f.
Proof. exact (EQ_MP (@lem4770687 A B f) (@lem4770686 A B f h1)). Qed.
Lemma lem4770689 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term6 A B) : term9 A B f s.
Proof. exact (@lem4770688 A B f h1 s). Qed.
Lemma lem4770690 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term9 A B f s) = (term10 A B f s).
Proof. exact (eq_refl (term9 A B f s)). Qed.
Lemma lem4770691 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term6 A B) : term10 A B f s.
Proof. exact (EQ_MP (@lem4770690 A B f s) (@lem4770689 A B f s h1)). Qed.
Lemma lem4770692 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term11 A B s f) : term11 A B s f.
Proof. exact (h1). Qed.
Lemma lem4770693 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term6 A B) (h2 : term11 A B s f) : term12 A B f s.
Proof. exact (@lem4770691 A B f s h1 (@lem4770692 A B s f h2)). Qed.
Lemma lem4770694 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term11 A B s f) : term13 A B f s.
Proof. exact (fun h0 : term6 A B => @lem4770693 A B s f h0 h1). Qed.
Lemma lem4770695 {A B : Type'} (h1 : term6 A B) : term6 A B.
Proof. exact (h1). Qed.
Lemma lem4770696 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term6 A B) (h2 : term11 A B s f) : term12 A B f s.
Proof. exact (@lem4770694 A B s f h2 (@lem4770695 A B h1)). Qed.
Lemma lem4770697 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term6 A B) : term10 A B f s.
Proof. exact (fun h0 : term11 A B s f => @lem4770696 A B s f h1 h0). Qed.
Lemma lem4770698 {A B : Type'} (f : A -> B) (h1 : term6 A B) : term8 A B f.
Proof. exact (fun s : A -> Prop => @lem4770697 A B f s h1). Qed.
Lemma lem4770699 {A B : Type'} (h1 : term6 A B) : term6 A B.
Proof. exact (fun f : A -> B => @lem4770698 A B f h1). Qed.
Lemma lem4770700 {A B : Type'} : term14 A B.
Proof. exact (fun h0 : term6 A B => @lem4770699 A B h0). Qed.
Lemma lem4770701 {A B : Type'} : term6 A B.
Proof. exact (@lem4770700 A B (@lem3626961 A B)). Qed.
Lemma lem4770702 {A B : Type'} (f : A -> B) : term7 A B f.
Proof. exact (@lem4770701 A B f). Qed.
Lemma lem4770703 {A B : Type'} (f : A -> B) : (term7 A B f) = (term8 A B f).
Proof. exact (eq_refl (term7 A B f)). Qed.
Lemma lem4770704 {A B : Type'} (f : A -> B) : term8 A B f.
Proof. exact (EQ_MP (@lem4770703 A B f) (@lem4770702 A B f)). Qed.
Lemma lem4770705 {A B : Type'} (f : A -> B) (s : A -> Prop) : term9 A B f s.
Proof. exact (@lem4770704 A B f s). Qed.
Lemma lem4770706 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term9 A B f s) = (term10 A B f s).
Proof. exact (eq_refl (term9 A B f s)). Qed.
Lemma lem4770708 (s : nat -> Prop) : term15 s.
Proof. exact (@lem4770658 s). Qed.
Lemma lem4770709 (s : nat -> Prop) : (term15 s) = (term16 s).
Proof. exact (eq_refl (term15 s)). Qed.
Lemma lem4770710 (s : nat -> Prop) : term16 s.
Proof. exact (EQ_MP (@lem4770709 s) (@lem4770708 s)). Qed.
Lemma lem4770711 (s : nat -> Prop) : (term16 s) = ((term16 s) = True).
Proof. exact (@lem7 (term16 s)). Qed.
Lemma lem4770714 (s : nat -> Prop) : (term16 s) = True.
Proof. exact (EQ_MP (@lem4770711 s) (@lem4770710 s)). Qed.
Lemma lem4770715 (s : nat -> Prop) : True = (term16 s).
Proof. exact (SYM (@lem4770714 s)). Qed.
Lemma lem4770716 (s : nat -> Prop) : term16 s.
Proof. exact (EQ_MP (@lem4770715 s) (@lem0)). Qed.
Lemma lem4770739 (s : nat -> Prop) (h1 : term17 s) : term17 s.
Proof. exact (h1). Qed.
Lemma lem4770740 (r : nat -> nat) (s : nat -> Prop) (h1 : term18 r s) : term18 r s.
Proof. exact (h1). Qed.
Lemma lem4770747 (r : nat -> nat) (s : nat -> Prop) (h1 : (@IMAGE nat nat r (@UNIV nat)) = s) : (@IMAGE nat nat r (@UNIV nat)) = s.
Proof. exact (h1). Qed.
Lemma lem4770748 (r : nat -> nat) (s : nat -> Prop) (h1 : (@IMAGE nat nat r (@UNIV nat)) = s) : s = (@IMAGE nat nat r (@UNIV nat)).
Proof. exact (SYM (@lem4770747 r s h1)). Qed.
Lemma lem4770749 (s : nat -> Prop) (r : nat -> nat) (h1 : s = (@IMAGE nat nat r (@UNIV nat))) : s = (@IMAGE nat nat r (@UNIV nat)).
Proof. exact (h1). Qed.
Lemma lem4770750 (s : nat -> Prop) (r : nat -> nat) (h1 : s = (@IMAGE nat nat r (@UNIV nat))) : (@IMAGE nat nat r (@UNIV nat)) = s.
Proof. exact (SYM (@lem4770749 s r h1)). Qed.
Lemma lem4770751 (s : nat -> Prop) (r : nat -> nat) : ((@IMAGE nat nat r (@UNIV nat)) = s) = (s = (@IMAGE nat nat r (@UNIV nat))).
Proof. exact (prop_ext (fun h1 : (@IMAGE nat nat r (@UNIV nat)) = s => @lem4770748 r s h1) (fun h1 : s = (@IMAGE nat nat r (@UNIV nat)) => @lem4770750 s r h1)). Qed.
Lemma lem4770752 (r : nat -> nat) : (term19 r) = (term19 r).
Proof. exact (eq_refl (term19 r)). Qed.
Lemma lem4770753 (s : nat -> Prop) (r : nat -> nat) : (term18 r s) = (term20 s r).
Proof. exact (MK_COMB (@lem4770752 r) (@lem4770751 s r)). Qed.
Lemma lem4770754 (r : nat -> nat) (s : nat -> Prop) (h1 : term18 r s) : term20 s r.
Proof. exact (EQ_MP (@lem4770753 s r) (@lem4770740 r s h1)). Qed.
Lemma lem4770755 (s : nat -> Prop) (r : nat -> nat) (h1 : s = (@IMAGE nat nat r (@UNIV nat))) : s = (@IMAGE nat nat r (@UNIV nat)).
Proof. exact (h1). Qed.
Lemma lem4770756 (r : nat -> nat) (h1 : term21 r) : term21 r.
Proof. exact (h1). Qed.
Lemma lem4770766 (s : nat -> Prop) (r : nat -> nat) (h1 : s = (@IMAGE nat nat r (@UNIV nat))) : s = (@IMAGE nat nat r (@UNIV nat)).
Proof. exact (h1). Qed.
Lemma lem4770767 : (@INFINITE nat) = (@INFINITE nat).
Proof. exact (eq_refl (@INFINITE nat)). Qed.
Lemma lem4770768 (s : nat -> Prop) (r : nat -> nat) (h1 : s = (@IMAGE nat nat r (@UNIV nat))) : (@INFINITE nat s) = (term22 r).
Proof. exact (MK_COMB (@lem4770767) (@lem4770766 s r h1)). Qed.
Lemma lem4770769 (s : nat -> Prop) (r : nat -> nat) (h1 : s = (@IMAGE nat nat r (@UNIV nat))) : (term22 r) = (@INFINITE nat s).
Proof. exact (SYM (@lem4770768 s r h1)). Qed.
Lemma lem4770771 {A B : Type'} (f : A -> B) (s : A -> Prop) : term10 A B f s.
Proof. exact (EQ_MP (@lem4770706 A B f s) (@lem4770705 A B f s)). Qed.
Lemma lem4770772 (f : nat -> nat) (s : nat -> Prop) : term23 f s.
Proof. exact (@lem4770771 nat nat f s). Qed.
Lemma lem4770773 (r : nat -> nat) : term24 r.
Proof. exact (@lem4770772 r (@UNIV nat)). Qed.
Lemma lem4770777 : (@INFINITE nat (@UNIV nat)) = True.
Proof. exact (EQ_MP (@lem4770683) (@lem4629194)). Qed.
Lemma lem4770778 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4770779 : term25 = (and True).
Proof. exact (MK_COMB (@lem4770778) (@lem4770777)). Qed.
Lemma lem4770793 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem4770681 A x) (@lem4770680 A x)). Qed.
Lemma lem4770794 (x : nat) : (@IN nat x (@UNIV nat)) = True.
Proof. exact (@lem4770793 nat x). Qed.
Lemma lem4770795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4770796 (x : nat) : (term26 x) = (and True).
Proof. exact (MK_COMB (@lem4770795) (@lem4770794 x)). Qed.
Lemma lem4770800 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem4770681 A x) (@lem4770680 A x)). Qed.
Lemma lem4770801 (x : nat) : (@IN nat x (@UNIV nat)) = True.
Proof. exact (@lem4770800 nat x). Qed.
Lemma lem4770802 (y : nat) : (@IN nat y (@UNIV nat)) = True.
Proof. exact (@lem4770801 y). Qed.
Lemma lem4770803 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4770804 (y : nat) : (term26 y) = (and True).
Proof. exact (MK_COMB (@lem4770803) (@lem4770802 y)). Qed.
Lemma lem4770807 (x : nat) (r : nat -> nat) (y : nat) : ((r x) = (r y)) = ((r x) = (r y)).
Proof. exact (eq_refl ((r x) = (r y))). Qed.
Lemma lem4770808 (x : nat) (r : nat -> nat) (y : nat) : (term27 x r y) = (term28 x r y).
Proof. exact (MK_COMB (@lem4770804 y) (@lem4770807 x r y)). Qed.
Lemma lem4770810 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4770811 (x : nat) (r : nat -> nat) (y : nat) : (term28 x r y) = ((r x) = (r y)).
Proof. exact (@lem4770810 ((r x) = (r y))). Qed.
Lemma lem4770814 (x : nat) (r : nat -> nat) (y : nat) : (term27 x r y) = ((r x) = (r y)).
Proof. exact (TRANS (@lem4770808 x r y) (@lem4770811 x r y)). Qed.
Lemma lem4770815 (x : nat) (r : nat -> nat) (y : nat) : (term29 x r y) = (term28 x r y).
Proof. exact (MK_COMB (@lem4770796 x) (@lem4770814 x r y)). Qed.
Lemma lem4770817 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4770818 (x : nat) (r : nat -> nat) (y : nat) : (term28 x r y) = ((r x) = (r y)).
Proof. exact (@lem4770817 ((r x) = (r y))). Qed.
Lemma lem4770821 (x : nat) (r : nat -> nat) (y : nat) : (term29 x r y) = ((r x) = (r y)).
Proof. exact (TRANS (@lem4770815 x r y) (@lem4770818 x r y)). Qed.
Lemma lem4770822 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4770823 (x : nat) (r : nat -> nat) (y : nat) : (term30 x r y) = (term31 x r y).
Proof. exact (MK_COMB (@lem4770822) (@lem4770821 x r y)). Qed.
Lemma lem4770826 (x : nat) (y : nat) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4770827 (r : nat -> nat) (x : nat) (y : nat) : (term32 r x y) = (term33 r x y).
Proof. exact (MK_COMB (@lem4770823 x r y) (@lem4770826 x y)). Qed.
Lemma lem4770832 (r : nat -> nat) (x : nat) : (term34 r x) = (term35 r x).
Proof. exact (fun_ext (fun y : nat => @lem4770827 r x y)). Qed.
Lemma lem4770833 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4770834 (r : nat -> nat) (x : nat) : (term36 r x) = (term37 r x).
Proof. exact (MK_COMB (@lem4770833) (@lem4770832 r x)). Qed.
Lemma lem4770839 (r : nat -> nat) : (term38 r) = (term39 r).
Proof. exact (fun_ext (fun x : nat => @lem4770834 r x)). Qed.
Lemma lem4770840 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4770841 (r : nat -> nat) : (term40 r) = (term41 r).
Proof. exact (MK_COMB (@lem4770840) (@lem4770839 r)). Qed.
Lemma lem4770846 (r : nat -> nat) : (term42 r) = (term43 r).
Proof. exact (MK_COMB (@lem4770779) (@lem4770841 r)). Qed.
Lemma lem4770848 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4770849 (r : nat -> nat) : (term43 r) = (term41 r).
Proof. exact (@lem4770848 (term41 r)). Qed.
Lemma lem4770866 (r : nat -> nat) : (term42 r) = (term41 r).
Proof. exact (TRANS (@lem4770846 r) (@lem4770849 r)). Qed.
Lemma lem4770867 (r : nat -> nat) : (term41 r) = (term42 r).
Proof. exact (SYM (@lem4770866 r)). Qed.
Lemma lem4770869 (P : type1605) : term0 P.
Proof. exact (@lem4770676 P (@lem111142 P)). Qed.
Lemma lem4770870 (r : nat -> nat) : term44 r.
Proof. exact (@lem4770869 (term45 r)). Qed.
Lemma lem4770871 (r : nat -> nat) (x : nat) : (term46 r x) = (term35 r x).
Proof. exact (eq_refl (term46 r x)). Qed.
Lemma lem4770872 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4770873 (r : nat -> nat) (x : nat) : (term47 r x) = (term48 r x).
Proof. exact (MK_COMB (@lem4770871 r x) (@lem4770872 x)). Qed.
Lemma lem4770874 (r : nat -> nat) (x : nat) : (term48 r x) = (term49 r x).
Proof. exact (eq_refl (term48 r x)). Qed.
Lemma lem4770875 (r : nat -> nat) (x : nat) : (term47 r x) = (term49 r x).
Proof. exact (TRANS (@lem4770873 r x) (@lem4770874 r x)). Qed.
Lemma lem4770876 (r : nat -> nat) : (term50 r) = (term51 r).
Proof. exact (fun_ext (fun x : nat => @lem4770875 r x)). Qed.
Lemma lem4770877 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4770878 (r : nat -> nat) : (term52 r) = (term53 r).
Proof. exact (MK_COMB (@lem4770877) (@lem4770876 r)). Qed.
Lemma lem4770879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4770880 (r : nat -> nat) : (term54 r) = (term55 r).
Proof. exact (MK_COMB (@lem4770879) (@lem4770878 r)). Qed.
Lemma lem4770881 (r : nat -> nat) (x : nat) : (term46 r x) = (term35 r x).
Proof. exact (eq_refl (term46 r x)). Qed.
Lemma lem4770882 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4770883 (r : nat -> nat) (x : nat) (n : nat) : (term56 r x n) = (term57 r x n).
Proof. exact (MK_COMB (@lem4770881 r x) (@lem4770882 n)). Qed.
Lemma lem4770884 (r : nat -> nat) (x : nat) (n : nat) : (term57 r x n) = (term33 r x n).
Proof. exact (eq_refl (term57 r x n)). Qed.
Lemma lem4770885 (r : nat -> nat) (x : nat) (n : nat) : (term56 r x n) = (term33 r x n).
Proof. exact (TRANS (@lem4770883 r x n) (@lem4770884 r x n)). Qed.
Lemma lem4770886 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4770887 (r : nat -> nat) (x : nat) (n : nat) : (term58 r x n) = (term59 r x n).
Proof. exact (MK_COMB (@lem4770886) (@lem4770885 r x n)). Qed.
Lemma lem4770888 (r : nat -> nat) (n : nat) : (term46 r n) = (term35 r n).
Proof. exact (eq_refl (term46 r n)). Qed.
Lemma lem4770889 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4770890 (r : nat -> nat) (n : nat) (x : nat) : (term56 r n x) = (term57 r n x).
Proof. exact (MK_COMB (@lem4770888 r n) (@lem4770889 x)). Qed.
Lemma lem4770891 (r : nat -> nat) (n : nat) (x : nat) : (term57 r n x) = (term33 r n x).
Proof. exact (eq_refl (term57 r n x)). Qed.
Lemma lem4770892 (r : nat -> nat) (n : nat) (x : nat) : (term56 r n x) = (term33 r n x).
Proof. exact (TRANS (@lem4770890 r n x) (@lem4770891 r n x)). Qed.
Lemma lem4770893 (r : nat -> nat) (n : nat) (x : nat) : ((term56 r x n) = (term56 r n x)) = ((term33 r x n) = (term33 r n x)).
Proof. exact (MK_COMB (@lem4770887 r x n) (@lem4770892 r n x)). Qed.
Lemma lem4770894 (r : nat -> nat) (x : nat) : (term60 r x) = (term61 r x).
Proof. exact (fun_ext (fun n : nat => @lem4770893 r n x)). Qed.
Lemma lem4770895 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4770896 (r : nat -> nat) (x : nat) : (term62 r x) = (term63 r x).
Proof. exact (MK_COMB (@lem4770895) (@lem4770894 r x)). Qed.
Lemma lem4770897 (r : nat -> nat) : (term64 r) = (term65 r).
Proof. exact (fun_ext (fun x : nat => @lem4770896 r x)). Qed.
Lemma lem4770898 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4770899 (r : nat -> nat) : (term66 r) = (term67 r).
Proof. exact (MK_COMB (@lem4770898) (@lem4770897 r)). Qed.
Lemma lem4770900 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4770901 (r : nat -> nat) : (term68 r) = (term69 r).
Proof. exact (MK_COMB (@lem4770900) (@lem4770899 r)). Qed.
Lemma lem4770902 (r : nat -> nat) (x : nat) : (term46 r x) = (term35 r x).
Proof. exact (eq_refl (term46 r x)). Qed.
Lemma lem4770903 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4770904 (r : nat -> nat) (x : nat) (n : nat) : (term56 r x n) = (term57 r x n).
Proof. exact (MK_COMB (@lem4770902 r x) (@lem4770903 n)). Qed.
Lemma lem4770905 (r : nat -> nat) (x : nat) (n : nat) : (term57 r x n) = (term33 r x n).
Proof. exact (eq_refl (term57 r x n)). Qed.
Lemma lem4770906 (r : nat -> nat) (x : nat) (n : nat) : (term56 r x n) = (term33 r x n).
Proof. exact (TRANS (@lem4770904 r x n) (@lem4770905 r x n)). Qed.
Lemma lem4770907 (x : nat) (n : nat) : (term70 x n) = (term70 x n).
Proof. exact (eq_refl (term70 x n)). Qed.
Lemma lem4770908 (r : nat -> nat) (x : nat) (n : nat) : (term71 r x n) = (term72 r x n).
Proof. exact (MK_COMB (@lem4770907 x n) (@lem4770906 r x n)). Qed.
Lemma lem4770909 (r : nat -> nat) (x : nat) : (term73 r x) = (term74 r x).
Proof. exact (fun_ext (fun n : nat => @lem4770908 r x n)). Qed.
Lemma lem4770910 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4770911 (r : nat -> nat) (x : nat) : (term75 r x) = (term76 r x).
Proof. exact (MK_COMB (@lem4770910) (@lem4770909 r x)). Qed.
Lemma lem4770912 (r : nat -> nat) : (term77 r) = (term78 r).
Proof. exact (fun_ext (fun x : nat => @lem4770911 r x)). Qed.
Lemma lem4770913 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4770914 (r : nat -> nat) : (term79 r) = (term80 r).
Proof. exact (MK_COMB (@lem4770913) (@lem4770912 r)). Qed.
Lemma lem4770915 (r : nat -> nat) : (term81 r) = (term82 r).
Proof. exact (MK_COMB (@lem4770901 r) (@lem4770914 r)). Qed.
Lemma lem4770916 (r : nat -> nat) : (term83 r) = (term84 r).
Proof. exact (MK_COMB (@lem4770880 r) (@lem4770915 r)). Qed.
Lemma lem4770917 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4770918 (r : nat -> nat) : (term85 r) = (term86 r).
Proof. exact (MK_COMB (@lem4770917) (@lem4770916 r)). Qed.
Lemma lem4770919 (r : nat -> nat) (x : nat) : (term46 r x) = (term35 r x).
Proof. exact (eq_refl (term46 r x)). Qed.
Lemma lem4770920 (y : nat) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4770921 (r : nat -> nat) (x : nat) (y : nat) : (term56 r x y) = (term57 r x y).
Proof. exact (MK_COMB (@lem4770919 r x) (@lem4770920 y)). Qed.
Lemma lem4770922 (r : nat -> nat) (x : nat) (y : nat) : (term57 r x y) = (term33 r x y).
Proof. exact (eq_refl (term57 r x y)). Qed.
Lemma lem4770923 (r : nat -> nat) (x : nat) (y : nat) : (term56 r x y) = (term33 r x y).
Proof. exact (TRANS (@lem4770921 r x y) (@lem4770922 r x y)). Qed.
Lemma lem4770924 (r : nat -> nat) (x : nat) : (term87 r x) = (term35 r x).
Proof. exact (fun_ext (fun y : nat => @lem4770923 r x y)). Qed.
Lemma lem4770925 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4770926 (r : nat -> nat) (x : nat) : (term88 r x) = (term37 r x).
Proof. exact (MK_COMB (@lem4770925) (@lem4770924 r x)). Qed.
Lemma lem4770927 (r : nat -> nat) : (term89 r) = (term39 r).
Proof. exact (fun_ext (fun x : nat => @lem4770926 r x)). Qed.
Lemma lem4770928 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4770929 (r : nat -> nat) : (term90 r) = (term41 r).
Proof. exact (MK_COMB (@lem4770928) (@lem4770927 r)). Qed.
Lemma lem4770930 (r : nat -> nat) : (term44 r) = (term91 r).
Proof. exact (MK_COMB (@lem4770918 r) (@lem4770929 r)). Qed.
Lemma lem4770931 (r : nat -> nat) : term91 r.
Proof. exact (EQ_MP (@lem4770930 r) (@lem4770870 r)). Qed.
Lemma lem4770933 (p : Prop) : p = (term92 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4770934 (r : nat -> nat) : (term84 r) = (term93 r).
Proof. exact (@lem4770933 (term84 r)). Qed.
Lemma lem4770935 (r : nat -> nat) : (term93 r) = (term84 r).
Proof. exact (SYM (@lem4770934 r)). Qed.
Lemma lem4770936 (r : nat -> nat) (h1 : term94 r) : term94 r.
Proof. exact (h1). Qed.
Lemma lem4770939 (s : nat -> Prop) (r : nat -> nat) (h1 : term95 s r) : term95 s r.
Proof. exact (h1). Qed.
Lemma lem4770940 (s : nat -> Prop) (r : nat -> nat) : term96 s r.
Proof. exact (fun h0 : term95 s r => @lem4770939 s r h0). Qed.
Lemma lem4770941 (s : nat -> Prop) (r : nat -> nat) (h1 : term96 s r) : term96 s r.
Proof. exact (h1). Qed.
Lemma lem4770942 (s : nat -> Prop) (r : nat -> nat) (h1 : term95 s r) : term95 s r.
Proof. exact (h1). Qed.
Lemma lem4770943 (s : nat -> Prop) (r : nat -> nat) (h1 : term95 s r) (h2 : term96 s r) : term95 s r.
Proof. exact (@lem4770941 s r h2 (@lem4770942 s r h1)). Qed.
Lemma lem4770944 (s : nat -> Prop) (r : nat -> nat) (h1 : term95 s r) : term97 s r.
Proof. exact (fun h0 : term96 s r => @lem4770943 s r h1 h0). Qed.
Lemma lem4770945 (s : nat -> Prop) (r : nat -> nat) (h1 : term96 s r) : term96 s r.
Proof. exact (h1). Qed.
Lemma lem4770946 (s : nat -> Prop) (r : nat -> nat) (h1 : term95 s r) (h2 : term96 s r) : term95 s r.
Proof. exact (@lem4770944 s r h1 (@lem4770945 s r h2)). Qed.
Lemma lem4770947 (s : nat -> Prop) (r : nat -> nat) (h1 : term96 s r) : term96 s r.
Proof. exact (fun h0 : term95 s r => @lem4770946 s r h0 h1). Qed.
Lemma lem4770948 (s : nat -> Prop) (r : nat -> nat) : term98 s r.
Proof. exact (fun h0 : term96 s r => @lem4770947 s r h0). Qed.
Lemma lem4770951 (s : nat -> Prop) (r : nat -> nat) : term96 s r.
Proof. exact (@lem4770948 s r (@lem4770940 s r)). Qed.
Lemma lem4771011 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4771012 : term99 = term100.
Proof. exact (@lem4771011 term101). Qed.
Lemma lem4771017 (r : nat -> nat) : (term102 r) = (term102 r).
Proof. exact (eq_refl (term102 r)). Qed.
Lemma lem4771018 (r : nat -> nat) : (term103 r) = (term104 r).
Proof. exact (MK_COMB (@lem4771017 r) (@lem4771012)). Qed.
Lemma lem4771021 (s : nat -> Prop) (r : nat -> nat) : (term105 s r) = (term105 s r).
Proof. exact (eq_refl (term105 s r)). Qed.
Lemma lem4771022 (s : nat -> Prop) (r : nat -> nat) : (term106 s r) = (term107 s r).
Proof. exact (MK_COMB (@lem4771021 s r) (@lem4771018 r)). Qed.
Lemma lem4771025 (r : nat -> nat) : (term108 r) = (term108 r).
Proof. exact (eq_refl (term108 r)). Qed.
Lemma lem4771026 (s : nat -> Prop) (r : nat -> nat) : (term95 s r) = (term109 s r).
Proof. exact (MK_COMB (@lem4771025 r) (@lem4771022 s r)). Qed.
Lemma lem4771029 (r : nat -> nat) : (term110 r) = (term111 r).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4771026 s r)). Qed.
Lemma lem4771030 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4771031 (r : nat -> nat) : (term112 r) = (term113 r).
Proof. exact (MK_COMB (@lem4771030) (@lem4771029 r)). Qed.
Lemma lem4771036 : term114 = term115.
Proof. exact (fun_ext (fun r : nat -> nat => @lem4771031 r)). Qed.
Lemma lem4771037 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem4771046 : term116 = term117.
Proof. exact (MK_COMB (@lem4771037) (@lem4771036)). Qed.
Lemma lem4771049 (n : nat) : (term118 n) = (term118 n).
Proof. exact (eq_refl (term118 n)). Qed.
Lemma lem4771050 : term119 = term119.
Proof. exact (fun_ext (fun n : nat => @lem4771049 n)). Qed.
Lemma lem4771051 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4771052 : term101 = term101.
Proof. exact (MK_COMB (@lem4771051) (@lem4771050)). Qed.
Lemma lem4771053 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4771054 : term100 = term100.
Proof. exact (MK_COMB (@lem4771053) (@lem4771052)). Qed.
Lemma lem4771063 (r : nat -> nat) (x : nat) (n : nat) : (term72 r x n) = (term72 r x n).
Proof. exact (eq_refl (term72 r x n)). Qed.
Lemma lem4771064 (r : nat -> nat) (x : nat) : (term74 r x) = (term74 r x).
Proof. exact (fun_ext (fun n : nat => @lem4771063 r x n)). Qed.
Lemma lem4771065 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4771066 (r : nat -> nat) (x : nat) : (term76 r x) = (term76 r x).
Proof. exact (MK_COMB (@lem4771065) (@lem4771064 r x)). Qed.
Lemma lem4771067 (r : nat -> nat) : (term78 r) = (term78 r).
Proof. exact (fun_ext (fun x : nat => @lem4771066 r x)). Qed.
Lemma lem4771068 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4771069 (r : nat -> nat) : (term80 r) = (term80 r).
Proof. exact (MK_COMB (@lem4771068) (@lem4771067 r)). Qed.
Lemma lem4771082 (r : nat -> nat) (n : nat) (x : nat) : ((term33 r x n) = (term33 r n x)) = ((term33 r x n) = (term33 r n x)).
Proof. exact (eq_refl ((term33 r x n) = (term33 r n x))). Qed.
Lemma lem4771083 (r : nat -> nat) (x : nat) : (term61 r x) = (term61 r x).
Proof. exact (fun_ext (fun n : nat => @lem4771082 r n x)). Qed.
Lemma lem4771084 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4771085 (r : nat -> nat) (x : nat) : (term63 r x) = (term63 r x).
Proof. exact (MK_COMB (@lem4771084) (@lem4771083 r x)). Qed.
Lemma lem4771086 (r : nat -> nat) : (term65 r) = (term65 r).
Proof. exact (fun_ext (fun x : nat => @lem4771085 r x)). Qed.
Lemma lem4771087 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4771088 (r : nat -> nat) : (term67 r) = (term67 r).
Proof. exact (MK_COMB (@lem4771087) (@lem4771086 r)). Qed.
Lemma lem4771089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4771090 (r : nat -> nat) : (term69 r) = (term69 r).
Proof. exact (MK_COMB (@lem4771089) (@lem4771088 r)). Qed.
Lemma lem4771091 (r : nat -> nat) : (term82 r) = (term82 r).
Proof. exact (MK_COMB (@lem4771090 r) (@lem4771069 r)). Qed.
Lemma lem4771096 (r : nat -> nat) (x : nat) : (term49 r x) = (term49 r x).
Proof. exact (eq_refl (term49 r x)). Qed.
Lemma lem4771097 (r : nat -> nat) : (term51 r) = (term51 r).
Proof. exact (fun_ext (fun x : nat => @lem4771096 r x)). Qed.
Lemma lem4771098 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4771099 (r : nat -> nat) : (term53 r) = (term53 r).
Proof. exact (MK_COMB (@lem4771098) (@lem4771097 r)). Qed.
Lemma lem4771100 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4771101 (r : nat -> nat) : (term55 r) = (term55 r).
Proof. exact (MK_COMB (@lem4771100) (@lem4771099 r)). Qed.
Lemma lem4771102 (r : nat -> nat) : (term84 r) = (term84 r).
Proof. exact (MK_COMB (@lem4771101 r) (@lem4771091 r)). Qed.
Lemma lem4771103 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4771104 (r : nat -> nat) : (term94 r) = (term94 r).
Proof. exact (MK_COMB (@lem4771103) (@lem4771102 r)). Qed.
Lemma lem4771105 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4771106 (r : nat -> nat) : (term102 r) = (term102 r).
Proof. exact (MK_COMB (@lem4771105) (@lem4771104 r)). Qed.
Lemma lem4771107 (r : nat -> nat) : (term104 r) = (term104 r).
Proof. exact (MK_COMB (@lem4771106 r) (@lem4771054)). Qed.
Lemma lem4771110 (s : nat -> Prop) (r : nat -> nat) : (term105 s r) = (term105 s r).
Proof. exact (eq_refl (term105 s r)). Qed.
Lemma lem4771111 (s : nat -> Prop) (r : nat -> nat) : (term107 s r) = (term107 s r).
Proof. exact (MK_COMB (@lem4771110 s r) (@lem4771107 r)). Qed.
Lemma lem4771116 (m : nat) (r : nat -> nat) (n : nat) : (term120 m r n) = (term120 m r n).
Proof. exact (eq_refl (term120 m r n)). Qed.
Lemma lem4771117 (m : nat) (r : nat -> nat) : (term121 m r) = (term121 m r).
Proof. exact (fun_ext (fun n : nat => @lem4771116 m r n)). Qed.
Lemma lem4771118 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4771119 (m : nat) (r : nat -> nat) : (term122 m r) = (term122 m r).
Proof. exact (MK_COMB (@lem4771118) (@lem4771117 m r)). Qed.
Lemma lem4771120 (r : nat -> nat) : (term123 r) = (term123 r).
Proof. exact (fun_ext (fun m : nat => @lem4771119 m r)). Qed.
Lemma lem4771121 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4771122 (r : nat -> nat) : (term21 r) = (term21 r).
Proof. exact (MK_COMB (@lem4771121) (@lem4771120 r)). Qed.
Lemma lem4771123 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4771124 (r : nat -> nat) : (term108 r) = (term108 r).
Proof. exact (MK_COMB (@lem4771123) (@lem4771122 r)). Qed.
Lemma lem4771125 (s : nat -> Prop) (r : nat -> nat) : (term109 s r) = (term109 s r).
Proof. exact (MK_COMB (@lem4771124 r) (@lem4771111 s r)). Qed.
Lemma lem4771126 (r : nat -> nat) : (term111 r) = (term111 r).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4771125 s r)). Qed.
Lemma lem4771127 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4771128 (r : nat -> nat) : (term113 r) = (term113 r).
Proof. exact (MK_COMB (@lem4771127) (@lem4771126 r)). Qed.
Lemma lem4771129 : term115 = term115.
Proof. exact (fun_ext (fun r : nat -> nat => @lem4771128 r)). Qed.
Lemma lem4771130 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem4771131 : term117 = term117.
Proof. exact (MK_COMB (@lem4771130) (@lem4771129)). Qed.
Lemma lem4771216 : term116 = term117.
Proof. exact (TRANS (@lem4771046) (@lem4771131)). Qed.
Lemma lem4771217 : term117 = term116.
Proof. exact (SYM (@lem4771216)). Qed.
Lemma lem4771218 (r : nat -> nat) (h1 : term21 r) : term21 r.
Proof. exact (h1). Qed.
Lemma lem4771220 (r : nat -> nat) (h1 : term94 r) : term94 r.
Proof. exact (h1). Qed.
Lemma lem4771221 (h1 : term101) : term101.
Proof. exact (h1). Qed.
Lemma lem4771228 (m : nat) (r : nat -> nat) (n : nat) : (term120 m r n) = (term124 m r n).
Proof. exact (@lem17265 (Peano.lt m n) (term125 m r n)). Qed.
Lemma lem4771229 (m : nat) (r : nat -> nat) : (term121 m r) = (term126 m r).
Proof. exact (fun_ext (fun n : nat => @lem4771228 m r n)). Qed.
Lemma lem4771230 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4771231 (m : nat) (r : nat -> nat) : (term122 m r) = (term127 m r).
Proof. exact (MK_COMB (@lem4771230) (@lem4771229 m r)). Qed.
Lemma lem4771232 (r : nat -> nat) : (term123 r) = (term128 r).
Proof. exact (fun_ext (fun m : nat => @lem4771231 m r)). Qed.
Lemma lem4771233 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4771290 (r : nat -> nat) : (term21 r) = (term129 r).
Proof. exact (MK_COMB (@lem4771233) (@lem4771232 r)). Qed.
Lemma lem4771291 (r : nat -> nat) (h1 : term21 r) : term129 r.
Proof. exact (EQ_MP (@lem4771290 r) (@lem4771218 r h1)). Qed.
Lemma lem4771304 (r : nat -> nat) (x : nat) : (term130 r x) = (term131 r x).
Proof. exact (@lem17362 ((r x) = (r x)) (x = x)). Qed.
Lemma lem4771305 (P : nat -> Prop) : (term132 P) = (term133 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4771306 (r : nat -> nat) : (term134 r) = (term135 r).
Proof. exact (@lem4771305 (term51 r)). Qed.
Lemma lem4771307 (r : nat -> nat) (x : nat) : (term136 r x) = (term49 r x).
Proof. exact (eq_refl (term136 r x)). Qed.
Lemma lem4771308 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4771309 (r : nat -> nat) (x : nat) : (term137 r x) = (term130 r x).
Proof. exact (MK_COMB (@lem4771308) (@lem4771307 r x)). Qed.
Lemma lem4771310 (r : nat -> nat) (x : nat) : (term137 r x) = (term131 r x).
Proof. exact (TRANS (@lem4771309 r x) (@lem4771304 r x)). Qed.
Lemma lem4771311 (r : nat -> nat) : (term138 r) = (term139 r).
Proof. exact (fun_ext (fun x : nat => @lem4771310 r x)). Qed.
Lemma lem4771312 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771313 (r : nat -> nat) : (term135 r) = (term140 r).
Proof. exact (MK_COMB (@lem4771312) (@lem4771311 r)). Qed.
Lemma lem4771314 (r : nat -> nat) : (term134 r) = (term140 r).
Proof. exact (TRANS (@lem4771306 r) (@lem4771313 r)). Qed.
Lemma lem4771323 (r : nat -> nat) (x : nat) (n : nat) : (term141 r x n) = (term142 r x n).
Proof. exact (@lem17362 ((r x) = (r n)) (x = n)). Qed.
Lemma lem4771328 (r : nat -> nat) (x : nat) (n : nat) : (term33 r x n) = (term143 r x n).
Proof. exact (@lem17265 ((r x) = (r n)) (x = n)). Qed.
Lemma lem4771337 (r : nat -> nat) (n : nat) (x : nat) : (term141 r n x) = (term142 r n x).
Proof. exact (@lem17362 ((r n) = (r x)) (n = x)). Qed.
Lemma lem4771342 (r : nat -> nat) (n : nat) (x : nat) : (term33 r n x) = (term143 r n x).
Proof. exact (@lem17265 ((r n) = (r x)) (n = x)). Qed.
Lemma lem4771343 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4771344 (r : nat -> nat) (x : nat) (n : nat) : (term144 r x n) = (term145 r x n).
Proof. exact (MK_COMB (@lem4771343) (@lem4771323 r x n)). Qed.
Lemma lem4771345 (r : nat -> nat) (n : nat) (x : nat) : (term146 r n x) = (term147 r n x).
Proof. exact (MK_COMB (@lem4771344 r x n) (@lem4771342 r n x)). Qed.
Lemma lem4771346 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4771347 (r : nat -> nat) (x : nat) (n : nat) : (term148 r x n) = (term149 r x n).
Proof. exact (MK_COMB (@lem4771346) (@lem4771328 r x n)). Qed.
Lemma lem4771348 (r : nat -> nat) (n : nat) (x : nat) : (term150 r n x) = (term151 r n x).
Proof. exact (MK_COMB (@lem4771347 r x n) (@lem4771337 r n x)). Qed.
Lemma lem4771349 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4771350 (r : nat -> nat) (n : nat) (x : nat) : (term152 r n x) = (term153 r n x).
Proof. exact (MK_COMB (@lem4771349) (@lem4771348 r n x)). Qed.
Lemma lem4771351 (r : nat -> nat) (n : nat) (x : nat) : (term154 r n x) = (term155 r n x).
Proof. exact (MK_COMB (@lem4771350 r n x) (@lem4771345 r n x)). Qed.
Lemma lem4771352 (r : nat -> nat) (n : nat) (x : nat) : (term156 r n x) = (term154 r n x).
Proof. exact (@lem17646 (term33 r x n) (term33 r n x)). Qed.
Lemma lem4771353 (r : nat -> nat) (n : nat) (x : nat) : (term156 r n x) = (term155 r n x).
Proof. exact (TRANS (@lem4771352 r n x) (@lem4771351 r n x)). Qed.
Lemma lem4771354 (P : nat -> Prop) : (term132 P) = (term133 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4771355 (r : nat -> nat) (x : nat) : (term157 r x) = (term158 r x).
Proof. exact (@lem4771354 (term61 r x)). Qed.
Lemma lem4771356 (r : nat -> nat) (n : nat) (x : nat) : (term159 r x n) = ((term33 r x n) = (term33 r n x)).
Proof. exact (eq_refl (term159 r x n)). Qed.
Lemma lem4771357 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4771358 (r : nat -> nat) (n : nat) (x : nat) : (term160 r x n) = (term156 r n x).
Proof. exact (MK_COMB (@lem4771357) (@lem4771356 r n x)). Qed.
Lemma lem4771359 (r : nat -> nat) (n : nat) (x : nat) : (term160 r x n) = (term155 r n x).
Proof. exact (TRANS (@lem4771358 r n x) (@lem4771353 r n x)). Qed.
Lemma lem4771360 (r : nat -> nat) (x : nat) : (term161 r x) = (term162 r x).
Proof. exact (fun_ext (fun n : nat => @lem4771359 r n x)). Qed.
Lemma lem4771361 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771362 (r : nat -> nat) (x : nat) : (term158 r x) = (term163 r x).
Proof. exact (MK_COMB (@lem4771361) (@lem4771360 r x)). Qed.
Lemma lem4771363 (r : nat -> nat) (x : nat) : (term157 r x) = (term163 r x).
Proof. exact (TRANS (@lem4771355 r x) (@lem4771362 r x)). Qed.
Lemma lem4771364 (P : nat -> Prop) : (term132 P) = (term133 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4771365 (r : nat -> nat) : (term164 r) = (term165 r).
Proof. exact (@lem4771364 (term65 r)). Qed.
Lemma lem4771366 (r : nat -> nat) (x : nat) : (term166 r x) = (term63 r x).
Proof. exact (eq_refl (term166 r x)). Qed.
Lemma lem4771367 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4771368 (r : nat -> nat) (x : nat) : (term167 r x) = (term157 r x).
Proof. exact (MK_COMB (@lem4771367) (@lem4771366 r x)). Qed.
Lemma lem4771369 (r : nat -> nat) (x : nat) : (term167 r x) = (term163 r x).
Proof. exact (TRANS (@lem4771368 r x) (@lem4771363 r x)). Qed.
Lemma lem4771370 (r : nat -> nat) : (term168 r) = (term169 r).
Proof. exact (fun_ext (fun x : nat => @lem4771369 r x)). Qed.
Lemma lem4771371 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771372 (r : nat -> nat) : (term165 r) = (term170 r).
Proof. exact (MK_COMB (@lem4771371) (@lem4771370 r)). Qed.
Lemma lem4771373 (r : nat -> nat) : (term164 r) = (term170 r).
Proof. exact (TRANS (@lem4771365 r) (@lem4771372 r)). Qed.
Lemma lem4771381 (r : nat -> nat) (x : nat) (n : nat) : (term141 r x n) = (term142 r x n).
Proof. exact (@lem17362 ((r x) = (r n)) (x = n)). Qed.
Lemma lem4771383 (x : nat) (n : nat) : (term171 x n) = (term171 x n).
Proof. exact (eq_refl (term171 x n)). Qed.
Lemma lem4771384 (r : nat -> nat) (x : nat) (n : nat) : (term172 r x n) = (term173 r x n).
Proof. exact (MK_COMB (@lem4771383 x n) (@lem4771381 r x n)). Qed.
Lemma lem4771385 (r : nat -> nat) (x : nat) (n : nat) : (term174 r x n) = (term172 r x n).
Proof. exact (@lem17362 (Peano.lt x n) (term33 r x n)). Qed.
Lemma lem4771386 (r : nat -> nat) (x : nat) (n : nat) : (term174 r x n) = (term173 r x n).
Proof. exact (TRANS (@lem4771385 r x n) (@lem4771384 r x n)). Qed.
Lemma lem4771387 (P : nat -> Prop) : (term132 P) = (term133 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4771388 (r : nat -> nat) (x : nat) : (term175 r x) = (term176 r x).
Proof. exact (@lem4771387 (term74 r x)). Qed.
Lemma lem4771389 (r : nat -> nat) (x : nat) (n : nat) : (term177 r x n) = (term72 r x n).
Proof. exact (eq_refl (term177 r x n)). Qed.
Lemma lem4771390 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4771391 (r : nat -> nat) (x : nat) (n : nat) : (term178 r x n) = (term174 r x n).
Proof. exact (MK_COMB (@lem4771390) (@lem4771389 r x n)). Qed.
Lemma lem4771392 (r : nat -> nat) (x : nat) (n : nat) : (term178 r x n) = (term173 r x n).
Proof. exact (TRANS (@lem4771391 r x n) (@lem4771386 r x n)). Qed.
Lemma lem4771393 (r : nat -> nat) (x : nat) : (term179 r x) = (term180 r x).
Proof. exact (fun_ext (fun n : nat => @lem4771392 r x n)). Qed.
Lemma lem4771394 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771395 (r : nat -> nat) (x : nat) : (term176 r x) = (term181 r x).
Proof. exact (MK_COMB (@lem4771394) (@lem4771393 r x)). Qed.
Lemma lem4771396 (r : nat -> nat) (x : nat) : (term175 r x) = (term181 r x).
Proof. exact (TRANS (@lem4771388 r x) (@lem4771395 r x)). Qed.
Lemma lem4771397 (P : nat -> Prop) : (term132 P) = (term133 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4771398 (r : nat -> nat) : (term182 r) = (term183 r).
Proof. exact (@lem4771397 (term78 r)). Qed.
Lemma lem4771399 (r : nat -> nat) (x : nat) : (term184 r x) = (term76 r x).
Proof. exact (eq_refl (term184 r x)). Qed.
Lemma lem4771400 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4771401 (r : nat -> nat) (x : nat) : (term185 r x) = (term175 r x).
Proof. exact (MK_COMB (@lem4771400) (@lem4771399 r x)). Qed.
Lemma lem4771402 (r : nat -> nat) (x : nat) : (term185 r x) = (term181 r x).
Proof. exact (TRANS (@lem4771401 r x) (@lem4771396 r x)). Qed.
Lemma lem4771403 (r : nat -> nat) : (term186 r) = (term187 r).
Proof. exact (fun_ext (fun x : nat => @lem4771402 r x)). Qed.
Lemma lem4771404 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771405 (r : nat -> nat) : (term183 r) = (term188 r).
Proof. exact (MK_COMB (@lem4771404) (@lem4771403 r)). Qed.
Lemma lem4771406 (r : nat -> nat) : (term182 r) = (term188 r).
Proof. exact (TRANS (@lem4771398 r) (@lem4771405 r)). Qed.
Lemma lem4771407 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4771408 (r : nat -> nat) : (term189 r) = (term190 r).
Proof. exact (MK_COMB (@lem4771407) (@lem4771373 r)). Qed.
Lemma lem4771409 (r : nat -> nat) : (term191 r) = (term192 r).
Proof. exact (MK_COMB (@lem4771408 r) (@lem4771406 r)). Qed.
Lemma lem4771410 (r : nat -> nat) : (term193 r) = (term191 r).
Proof. exact (@lem17045 (term67 r) (term80 r)). Qed.
Lemma lem4771411 (r : nat -> nat) : (term193 r) = (term192 r).
Proof. exact (TRANS (@lem4771410 r) (@lem4771409 r)). Qed.
Lemma lem4771412 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4771413 (r : nat -> nat) : (term194 r) = (term195 r).
Proof. exact (MK_COMB (@lem4771412) (@lem4771314 r)). Qed.
Lemma lem4771414 (r : nat -> nat) : (term196 r) = (term197 r).
Proof. exact (MK_COMB (@lem4771413 r) (@lem4771411 r)). Qed.
Lemma lem4771415 (r : nat -> nat) : (term94 r) = (term196 r).
Proof. exact (@lem17045 (term53 r) (term82 r)). Qed.
Lemma lem4771416 (r : nat -> nat) : (term94 r) = (term197 r).
Proof. exact (TRANS (@lem4771415 r) (@lem4771414 r)). Qed.
Lemma lem4771470 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4771471 (P : nat -> Prop) (Q : nat -> Prop) : (term200 P Q) = (term201 P Q).
Proof. exact (@lem4771470 nat P Q). Qed.
Lemma lem4771472 (r : nat -> nat) (x : nat) : (term202 r x) = (term203 r x).
Proof. exact (@lem4771471 (term204 r x) (term205 r x)). Qed.
Lemma lem4771473 (r : nat -> nat) (n : nat) (x : nat) : (term206 r x n) = (term151 r n x).
Proof. exact (eq_refl (term206 r x n)). Qed.
Lemma lem4771474 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4771475 (r : nat -> nat) (n : nat) (x : nat) : (term207 r x n) = (term153 r n x).
Proof. exact (MK_COMB (@lem4771474) (@lem4771473 r n x)). Qed.
Lemma lem4771476 (r : nat -> nat) (n : nat) (x : nat) : (term208 r x n) = (term147 r n x).
Proof. exact (eq_refl (term208 r x n)). Qed.
Lemma lem4771477 (r : nat -> nat) (n : nat) (x : nat) : (term209 r x n) = (term155 r n x).
Proof. exact (MK_COMB (@lem4771475 r n x) (@lem4771476 r n x)). Qed.
Lemma lem4771478 (r : nat -> nat) (x : nat) : (term210 r x) = (term162 r x).
Proof. exact (fun_ext (fun n : nat => @lem4771477 r n x)). Qed.
Lemma lem4771479 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771480 (r : nat -> nat) (x : nat) : (term202 r x) = (term163 r x).
Proof. exact (MK_COMB (@lem4771479) (@lem4771478 r x)). Qed.
Lemma lem4771481 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4771482 (r : nat -> nat) (x : nat) : (term211 r x) = (term212 r x).
Proof. exact (MK_COMB (@lem4771481) (@lem4771480 r x)). Qed.
Lemma lem4771483 (r : nat -> nat) (n : nat) (x : nat) : (term206 r x n) = (term151 r n x).
Proof. exact (eq_refl (term206 r x n)). Qed.
Lemma lem4771484 (r : nat -> nat) (x : nat) : (term213 r x) = (term204 r x).
Proof. exact (fun_ext (fun n : nat => @lem4771483 r n x)). Qed.
Lemma lem4771485 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771486 (r : nat -> nat) (x : nat) : (term214 r x) = (term215 r x).
Proof. exact (MK_COMB (@lem4771485) (@lem4771484 r x)). Qed.
Lemma lem4771487 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4771488 (r : nat -> nat) (x : nat) : (term216 r x) = (term217 r x).
Proof. exact (MK_COMB (@lem4771487) (@lem4771486 r x)). Qed.
Lemma lem4771489 (r : nat -> nat) (n : nat) (x : nat) : (term208 r x n) = (term147 r n x).
Proof. exact (eq_refl (term208 r x n)). Qed.
Lemma lem4771490 (r : nat -> nat) (x : nat) : (term218 r x) = (term205 r x).
Proof. exact (fun_ext (fun n : nat => @lem4771489 r n x)). Qed.
Lemma lem4771491 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771492 (r : nat -> nat) (x : nat) : (term219 r x) = (term220 r x).
Proof. exact (MK_COMB (@lem4771491) (@lem4771490 r x)). Qed.
Lemma lem4771493 (r : nat -> nat) (x : nat) : (term203 r x) = (term221 r x).
Proof. exact (MK_COMB (@lem4771488 r x) (@lem4771492 r x)). Qed.
Lemma lem4771494 (r : nat -> nat) (x : nat) : ((term202 r x) = (term203 r x)) = ((term163 r x) = (term221 r x)).
Proof. exact (MK_COMB (@lem4771482 r x) (@lem4771493 r x)). Qed.
Lemma lem4771495 (r : nat -> nat) (x : nat) : (term163 r x) = (term221 r x).
Proof. exact (EQ_MP (@lem4771494 r x) (@lem4771472 r x)). Qed.
Lemma lem4771592 (r : nat -> nat) : (term169 r) = (term222 r).
Proof. exact (fun_ext (fun x : nat => @lem4771495 r x)). Qed.
Lemma lem4771593 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771594 (r : nat -> nat) : (term170 r) = (term223 r).
Proof. exact (MK_COMB (@lem4771593) (@lem4771592 r)). Qed.
Lemma lem4771596 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4771597 (P : nat -> Prop) (Q : nat -> Prop) : (term200 P Q) = (term201 P Q).
Proof. exact (@lem4771596 nat P Q). Qed.
Lemma lem4771598 (r : nat -> nat) : (term224 r) = (term225 r).
Proof. exact (@lem4771597 (term226 r) (term227 r)). Qed.
Lemma lem4771599 (r : nat -> nat) (x : nat) : (term228 r x) = (term215 r x).
Proof. exact (eq_refl (term228 r x)). Qed.
Lemma lem4771600 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4771601 (r : nat -> nat) (x : nat) : (term229 r x) = (term217 r x).
Proof. exact (MK_COMB (@lem4771600) (@lem4771599 r x)). Qed.
Lemma lem4771602 (r : nat -> nat) (x : nat) : (term230 r x) = (term220 r x).
Proof. exact (eq_refl (term230 r x)). Qed.
Lemma lem4771603 (r : nat -> nat) (x : nat) : (term231 r x) = (term221 r x).
Proof. exact (MK_COMB (@lem4771601 r x) (@lem4771602 r x)). Qed.
Lemma lem4771604 (r : nat -> nat) : (term232 r) = (term222 r).
Proof. exact (fun_ext (fun x : nat => @lem4771603 r x)). Qed.
Lemma lem4771605 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771606 (r : nat -> nat) : (term224 r) = (term223 r).
Proof. exact (MK_COMB (@lem4771605) (@lem4771604 r)). Qed.
Lemma lem4771607 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4771608 (r : nat -> nat) : (term233 r) = (term234 r).
Proof. exact (MK_COMB (@lem4771607) (@lem4771606 r)). Qed.
Lemma lem4771609 (r : nat -> nat) (x : nat) : (term228 r x) = (term215 r x).
Proof. exact (eq_refl (term228 r x)). Qed.
Lemma lem4771610 (r : nat -> nat) : (term235 r) = (term226 r).
Proof. exact (fun_ext (fun x : nat => @lem4771609 r x)). Qed.
Lemma lem4771611 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771612 (r : nat -> nat) : (term236 r) = (term237 r).
Proof. exact (MK_COMB (@lem4771611) (@lem4771610 r)). Qed.
Lemma lem4771613 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4771614 (r : nat -> nat) : (term238 r) = (term239 r).
Proof. exact (MK_COMB (@lem4771613) (@lem4771612 r)). Qed.
Lemma lem4771615 (r : nat -> nat) (x : nat) : (term230 r x) = (term220 r x).
Proof. exact (eq_refl (term230 r x)). Qed.
Lemma lem4771616 (r : nat -> nat) : (term240 r) = (term227 r).
Proof. exact (fun_ext (fun x : nat => @lem4771615 r x)). Qed.
Lemma lem4771617 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771618 (r : nat -> nat) : (term241 r) = (term242 r).
Proof. exact (MK_COMB (@lem4771617) (@lem4771616 r)). Qed.
Lemma lem4771619 (r : nat -> nat) : (term225 r) = (term243 r).
Proof. exact (MK_COMB (@lem4771614 r) (@lem4771618 r)). Qed.
Lemma lem4771620 (r : nat -> nat) : ((term224 r) = (term225 r)) = ((term223 r) = (term243 r)).
Proof. exact (MK_COMB (@lem4771608 r) (@lem4771619 r)). Qed.
Lemma lem4771621 (r : nat -> nat) : (term223 r) = (term243 r).
Proof. exact (EQ_MP (@lem4771620 r) (@lem4771598 r)). Qed.
Lemma lem4771726 (r : nat -> nat) : (term170 r) = (term243 r).
Proof. exact (TRANS (@lem4771594 r) (@lem4771621 r)). Qed.
Lemma lem4771727 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4771728 (r : nat -> nat) : (term190 r) = (term244 r).
Proof. exact (MK_COMB (@lem4771727) (@lem4771726 r)). Qed.
Lemma lem4771781 (r : nat -> nat) : (term188 r) = (term188 r).
Proof. exact (eq_refl (term188 r)). Qed.
Lemma lem4771782 (r : nat -> nat) : (term192 r) = (term245 r).
Proof. exact (MK_COMB (@lem4771728 r) (@lem4771781 r)). Qed.
Lemma lem4771783 (r : nat -> nat) : (term195 r) = (term195 r).
Proof. exact (eq_refl (term195 r)). Qed.
Lemma lem4771784 (r : nat -> nat) : (term197 r) = (term246 r).
Proof. exact (MK_COMB (@lem4771783 r) (@lem4771782 r)). Qed.
Lemma lem4771786 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term199 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4771787 (P : nat -> Prop) (Q : nat -> Prop) : (term201 P Q) = (term200 P Q).
Proof. exact (@lem4771786 nat P Q). Qed.
Lemma lem4771788 (r : nat -> nat) : (term225 r) = (term224 r).
Proof. exact (@lem4771787 (term226 r) (term227 r)). Qed.
Lemma lem4771789 (r : nat -> nat) (x : nat) : (term228 r x) = (term215 r x).
Proof. exact (eq_refl (term228 r x)). Qed.
Lemma lem4771790 (r : nat -> nat) : (term235 r) = (term226 r).
Proof. exact (fun_ext (fun x : nat => @lem4771789 r x)). Qed.
Lemma lem4771791 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771792 (r : nat -> nat) : (term236 r) = (term237 r).
Proof. exact (MK_COMB (@lem4771791) (@lem4771790 r)). Qed.
Lemma lem4771793 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4771794 (r : nat -> nat) : (term238 r) = (term239 r).
Proof. exact (MK_COMB (@lem4771793) (@lem4771792 r)). Qed.
Lemma lem4771795 (r : nat -> nat) (x : nat) : (term230 r x) = (term220 r x).
Proof. exact (eq_refl (term230 r x)). Qed.
Lemma lem4771796 (r : nat -> nat) : (term240 r) = (term227 r).
Proof. exact (fun_ext (fun x : nat => @lem4771795 r x)). Qed.
Lemma lem4771797 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771798 (r : nat -> nat) : (term241 r) = (term242 r).
Proof. exact (MK_COMB (@lem4771797) (@lem4771796 r)). Qed.
Lemma lem4771799 (r : nat -> nat) : (term225 r) = (term243 r).
Proof. exact (MK_COMB (@lem4771794 r) (@lem4771798 r)). Qed.
Lemma lem4771800 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4771801 (r : nat -> nat) : (term247 r) = (term248 r).
Proof. exact (MK_COMB (@lem4771800) (@lem4771799 r)). Qed.
Lemma lem4771802 (r : nat -> nat) (x : nat) : (term228 r x) = (term215 r x).
Proof. exact (eq_refl (term228 r x)). Qed.
Lemma lem4771803 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4771804 (r : nat -> nat) (x : nat) : (term229 r x) = (term217 r x).
Proof. exact (MK_COMB (@lem4771803) (@lem4771802 r x)). Qed.
Lemma lem4771805 (r : nat -> nat) (x : nat) : (term230 r x) = (term220 r x).
Proof. exact (eq_refl (term230 r x)). Qed.
Lemma lem4771806 (r : nat -> nat) (x : nat) : (term231 r x) = (term221 r x).
Proof. exact (MK_COMB (@lem4771804 r x) (@lem4771805 r x)). Qed.
Lemma lem4771807 (r : nat -> nat) : (term232 r) = (term222 r).
Proof. exact (fun_ext (fun x : nat => @lem4771806 r x)). Qed.
Lemma lem4771808 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771809 (r : nat -> nat) : (term224 r) = (term223 r).
Proof. exact (MK_COMB (@lem4771808) (@lem4771807 r)). Qed.
Lemma lem4771810 (r : nat -> nat) : ((term225 r) = (term224 r)) = ((term243 r) = (term223 r)).
Proof. exact (MK_COMB (@lem4771801 r) (@lem4771809 r)). Qed.
Lemma lem4771811 (r : nat -> nat) : (term243 r) = (term223 r).
Proof. exact (EQ_MP (@lem4771810 r) (@lem4771788 r)). Qed.
Lemma lem4771813 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term199 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4771814 (P : nat -> Prop) (Q : nat -> Prop) : (term201 P Q) = (term200 P Q).
Proof. exact (@lem4771813 nat P Q). Qed.
Lemma lem4771815 (r : nat -> nat) (x : nat) : (term203 r x) = (term202 r x).
Proof. exact (@lem4771814 (term204 r x) (term205 r x)). Qed.
Lemma lem4771816 (r : nat -> nat) (n : nat) (x : nat) : (term206 r x n) = (term151 r n x).
Proof. exact (eq_refl (term206 r x n)). Qed.
Lemma lem4771817 (r : nat -> nat) (x : nat) : (term213 r x) = (term204 r x).
Proof. exact (fun_ext (fun n : nat => @lem4771816 r n x)). Qed.
Lemma lem4771818 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771819 (r : nat -> nat) (x : nat) : (term214 r x) = (term215 r x).
Proof. exact (MK_COMB (@lem4771818) (@lem4771817 r x)). Qed.
Lemma lem4771820 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4771821 (r : nat -> nat) (x : nat) : (term216 r x) = (term217 r x).
Proof. exact (MK_COMB (@lem4771820) (@lem4771819 r x)). Qed.
Lemma lem4771822 (r : nat -> nat) (n : nat) (x : nat) : (term208 r x n) = (term147 r n x).
Proof. exact (eq_refl (term208 r x n)). Qed.
Lemma lem4771823 (r : nat -> nat) (x : nat) : (term218 r x) = (term205 r x).
Proof. exact (fun_ext (fun n : nat => @lem4771822 r n x)). Qed.
Lemma lem4771824 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771825 (r : nat -> nat) (x : nat) : (term219 r x) = (term220 r x).
Proof. exact (MK_COMB (@lem4771824) (@lem4771823 r x)). Qed.
Lemma lem4771826 (r : nat -> nat) (x : nat) : (term203 r x) = (term221 r x).
Proof. exact (MK_COMB (@lem4771821 r x) (@lem4771825 r x)). Qed.
Lemma lem4771827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4771828 (r : nat -> nat) (x : nat) : (term249 r x) = (term250 r x).
Proof. exact (MK_COMB (@lem4771827) (@lem4771826 r x)). Qed.
Lemma lem4771829 (r : nat -> nat) (n : nat) (x : nat) : (term206 r x n) = (term151 r n x).
Proof. exact (eq_refl (term206 r x n)). Qed.
Lemma lem4771830 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4771831 (r : nat -> nat) (n : nat) (x : nat) : (term207 r x n) = (term153 r n x).
Proof. exact (MK_COMB (@lem4771830) (@lem4771829 r n x)). Qed.
Lemma lem4771832 (r : nat -> nat) (n : nat) (x : nat) : (term208 r x n) = (term147 r n x).
Proof. exact (eq_refl (term208 r x n)). Qed.
Lemma lem4771833 (r : nat -> nat) (n : nat) (x : nat) : (term209 r x n) = (term155 r n x).
Proof. exact (MK_COMB (@lem4771831 r n x) (@lem4771832 r n x)). Qed.
Lemma lem4771834 (r : nat -> nat) (x : nat) : (term210 r x) = (term162 r x).
Proof. exact (fun_ext (fun n : nat => @lem4771833 r n x)). Qed.
Lemma lem4771835 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771836 (r : nat -> nat) (x : nat) : (term202 r x) = (term163 r x).
Proof. exact (MK_COMB (@lem4771835) (@lem4771834 r x)). Qed.
Lemma lem4771837 (r : nat -> nat) (x : nat) : ((term203 r x) = (term202 r x)) = ((term221 r x) = (term163 r x)).
Proof. exact (MK_COMB (@lem4771828 r x) (@lem4771836 r x)). Qed.
Lemma lem4771838 (r : nat -> nat) (x : nat) : (term221 r x) = (term163 r x).
Proof. exact (EQ_MP (@lem4771837 r x) (@lem4771815 r x)). Qed.
Lemma lem4771839 (r : nat -> nat) : (term222 r) = (term169 r).
Proof. exact (fun_ext (fun x : nat => @lem4771838 r x)). Qed.
Lemma lem4771840 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771841 (r : nat -> nat) : (term223 r) = (term170 r).
Proof. exact (MK_COMB (@lem4771840) (@lem4771839 r)). Qed.
Lemma lem4771842 (r : nat -> nat) : (term243 r) = (term170 r).
Proof. exact (TRANS (@lem4771811 r) (@lem4771841 r)). Qed.
Lemma lem4771843 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4771844 (r : nat -> nat) : (term244 r) = (term190 r).
Proof. exact (MK_COMB (@lem4771843) (@lem4771842 r)). Qed.
Lemma lem4771845 (r : nat -> nat) : (term188 r) = (term188 r).
Proof. exact (eq_refl (term188 r)). Qed.
Lemma lem4771846 (r : nat -> nat) : (term245 r) = (term192 r).
Proof. exact (MK_COMB (@lem4771844 r) (@lem4771845 r)). Qed.
Lemma lem4771848 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term199 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4771849 (P : nat -> Prop) (Q : nat -> Prop) : (term201 P Q) = (term200 P Q).
Proof. exact (@lem4771848 nat P Q). Qed.
Lemma lem4771850 (r : nat -> nat) : (term251 r) = (term252 r).
Proof. exact (@lem4771849 (term169 r) (term187 r)). Qed.
Lemma lem4771851 (r : nat -> nat) (x : nat) : (term253 r x) = (term163 r x).
Proof. exact (eq_refl (term253 r x)). Qed.
Lemma lem4771852 (r : nat -> nat) : (term254 r) = (term169 r).
Proof. exact (fun_ext (fun x : nat => @lem4771851 r x)). Qed.
Lemma lem4771853 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771854 (r : nat -> nat) : (term255 r) = (term170 r).
Proof. exact (MK_COMB (@lem4771853) (@lem4771852 r)). Qed.
Lemma lem4771855 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4771856 (r : nat -> nat) : (term256 r) = (term190 r).
Proof. exact (MK_COMB (@lem4771855) (@lem4771854 r)). Qed.
Lemma lem4771857 (r : nat -> nat) (x : nat) : (term257 r x) = (term181 r x).
Proof. exact (eq_refl (term257 r x)). Qed.
Lemma lem4771858 (r : nat -> nat) : (term258 r) = (term187 r).
Proof. exact (fun_ext (fun x : nat => @lem4771857 r x)). Qed.
Lemma lem4771859 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771860 (r : nat -> nat) : (term259 r) = (term188 r).
Proof. exact (MK_COMB (@lem4771859) (@lem4771858 r)). Qed.
Lemma lem4771861 (r : nat -> nat) : (term251 r) = (term192 r).
Proof. exact (MK_COMB (@lem4771856 r) (@lem4771860 r)). Qed.
Lemma lem4771862 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4771863 (r : nat -> nat) : (term260 r) = (term261 r).
Proof. exact (MK_COMB (@lem4771862) (@lem4771861 r)). Qed.
Lemma lem4771864 (r : nat -> nat) (x : nat) : (term253 r x) = (term163 r x).
Proof. exact (eq_refl (term253 r x)). Qed.
Lemma lem4771865 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4771866 (r : nat -> nat) (x : nat) : (term262 r x) = (term263 r x).
Proof. exact (MK_COMB (@lem4771865) (@lem4771864 r x)). Qed.
Lemma lem4771867 (r : nat -> nat) (x : nat) : (term257 r x) = (term181 r x).
Proof. exact (eq_refl (term257 r x)). Qed.
Lemma lem4771868 (r : nat -> nat) (x : nat) : (term264 r x) = (term265 r x).
Proof. exact (MK_COMB (@lem4771866 r x) (@lem4771867 r x)). Qed.
Lemma lem4771869 (r : nat -> nat) : (term266 r) = (term267 r).
Proof. exact (fun_ext (fun x : nat => @lem4771868 r x)). Qed.
Lemma lem4771870 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771871 (r : nat -> nat) : (term252 r) = (term268 r).
Proof. exact (MK_COMB (@lem4771870) (@lem4771869 r)). Qed.
Lemma lem4771872 (r : nat -> nat) : ((term251 r) = (term252 r)) = ((term192 r) = (term268 r)).
Proof. exact (MK_COMB (@lem4771863 r) (@lem4771871 r)). Qed.
Lemma lem4771873 (r : nat -> nat) : (term192 r) = (term268 r).
Proof. exact (EQ_MP (@lem4771872 r) (@lem4771850 r)). Qed.
Lemma lem4771875 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term199 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4771876 (P : nat -> Prop) (Q : nat -> Prop) : (term201 P Q) = (term200 P Q).
Proof. exact (@lem4771875 nat P Q). Qed.
Lemma lem4771877 (r : nat -> nat) (x : nat) : (term269 r x) = (term270 r x).
Proof. exact (@lem4771876 (term162 r x) (term180 r x)). Qed.
Lemma lem4771878 (r : nat -> nat) (n : nat) (x : nat) : (term271 r x n) = (term155 r n x).
Proof. exact (eq_refl (term271 r x n)). Qed.
Lemma lem4771879 (r : nat -> nat) (x : nat) : (term272 r x) = (term162 r x).
Proof. exact (fun_ext (fun n : nat => @lem4771878 r n x)). Qed.
Lemma lem4771880 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771881 (r : nat -> nat) (x : nat) : (term273 r x) = (term163 r x).
Proof. exact (MK_COMB (@lem4771880) (@lem4771879 r x)). Qed.
Lemma lem4771882 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4771883 (r : nat -> nat) (x : nat) : (term274 r x) = (term263 r x).
Proof. exact (MK_COMB (@lem4771882) (@lem4771881 r x)). Qed.
Lemma lem4771884 (r : nat -> nat) (x : nat) (n : nat) : (term275 r x n) = (term173 r x n).
Proof. exact (eq_refl (term275 r x n)). Qed.
Lemma lem4771885 (r : nat -> nat) (x : nat) : (term276 r x) = (term180 r x).
Proof. exact (fun_ext (fun n : nat => @lem4771884 r x n)). Qed.
Lemma lem4771886 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771887 (r : nat -> nat) (x : nat) : (term277 r x) = (term181 r x).
Proof. exact (MK_COMB (@lem4771886) (@lem4771885 r x)). Qed.
Lemma lem4771888 (r : nat -> nat) (x : nat) : (term269 r x) = (term265 r x).
Proof. exact (MK_COMB (@lem4771883 r x) (@lem4771887 r x)). Qed.
Lemma lem4771889 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4771890 (r : nat -> nat) (x : nat) : (term278 r x) = (term279 r x).
Proof. exact (MK_COMB (@lem4771889) (@lem4771888 r x)). Qed.
Lemma lem4771891 (r : nat -> nat) (n : nat) (x : nat) : (term271 r x n) = (term155 r n x).
Proof. exact (eq_refl (term271 r x n)). Qed.
Lemma lem4771892 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4771893 (r : nat -> nat) (n : nat) (x : nat) : (term280 r x n) = (term281 r n x).
Proof. exact (MK_COMB (@lem4771892) (@lem4771891 r n x)). Qed.
Lemma lem4771894 (r : nat -> nat) (x : nat) (n : nat) : (term275 r x n) = (term173 r x n).
Proof. exact (eq_refl (term275 r x n)). Qed.
Lemma lem4771895 (r : nat -> nat) (x : nat) (n : nat) : (term282 r x n) = (term283 r x n).
Proof. exact (MK_COMB (@lem4771893 r n x) (@lem4771894 r x n)). Qed.
Lemma lem4771896 (r : nat -> nat) (x : nat) : (term284 r x) = (term285 r x).
Proof. exact (fun_ext (fun n : nat => @lem4771895 r x n)). Qed.
Lemma lem4771897 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771898 (r : nat -> nat) (x : nat) : (term270 r x) = (term286 r x).
Proof. exact (MK_COMB (@lem4771897) (@lem4771896 r x)). Qed.
Lemma lem4771899 (r : nat -> nat) (x : nat) : ((term269 r x) = (term270 r x)) = ((term265 r x) = (term286 r x)).
Proof. exact (MK_COMB (@lem4771890 r x) (@lem4771898 r x)). Qed.
Lemma lem4771900 (r : nat -> nat) (x : nat) : (term265 r x) = (term286 r x).
Proof. exact (EQ_MP (@lem4771899 r x) (@lem4771877 r x)). Qed.
Lemma lem4771901 (r : nat -> nat) : (term267 r) = (term287 r).
Proof. exact (fun_ext (fun x : nat => @lem4771900 r x)). Qed.
Lemma lem4771902 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771903 (r : nat -> nat) : (term268 r) = (term288 r).
Proof. exact (MK_COMB (@lem4771902) (@lem4771901 r)). Qed.
Lemma lem4771904 (r : nat -> nat) : (term192 r) = (term288 r).
Proof. exact (TRANS (@lem4771873 r) (@lem4771903 r)). Qed.
Lemma lem4771905 (r : nat -> nat) : (term245 r) = (term288 r).
Proof. exact (TRANS (@lem4771846 r) (@lem4771904 r)). Qed.
Lemma lem4771906 (r : nat -> nat) : (term195 r) = (term195 r).
Proof. exact (eq_refl (term195 r)). Qed.
Lemma lem4771907 (r : nat -> nat) : (term246 r) = (term289 r).
Proof. exact (MK_COMB (@lem4771906 r) (@lem4771905 r)). Qed.
Lemma lem4771909 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term199 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4771910 (P : nat -> Prop) (Q : nat -> Prop) : (term201 P Q) = (term200 P Q).
Proof. exact (@lem4771909 nat P Q). Qed.
Lemma lem4771911 (r : nat -> nat) : (term290 r) = (term291 r).
Proof. exact (@lem4771910 (term139 r) (term287 r)). Qed.
Lemma lem4771912 (r : nat -> nat) (x : nat) : (term292 r x) = (term131 r x).
Proof. exact (eq_refl (term292 r x)). Qed.
Lemma lem4771913 (r : nat -> nat) : (term293 r) = (term139 r).
Proof. exact (fun_ext (fun x : nat => @lem4771912 r x)). Qed.
Lemma lem4771914 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771915 (r : nat -> nat) : (term294 r) = (term140 r).
Proof. exact (MK_COMB (@lem4771914) (@lem4771913 r)). Qed.
Lemma lem4771916 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4771917 (r : nat -> nat) : (term295 r) = (term195 r).
Proof. exact (MK_COMB (@lem4771916) (@lem4771915 r)). Qed.
Lemma lem4771918 (r : nat -> nat) (x : nat) : (term296 r x) = (term286 r x).
Proof. exact (eq_refl (term296 r x)). Qed.
Lemma lem4771919 (r : nat -> nat) : (term297 r) = (term287 r).
Proof. exact (fun_ext (fun x : nat => @lem4771918 r x)). Qed.
Lemma lem4771920 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771921 (r : nat -> nat) : (term298 r) = (term288 r).
Proof. exact (MK_COMB (@lem4771920) (@lem4771919 r)). Qed.
Lemma lem4771922 (r : nat -> nat) : (term290 r) = (term289 r).
Proof. exact (MK_COMB (@lem4771917 r) (@lem4771921 r)). Qed.
Lemma lem4771923 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4771924 (r : nat -> nat) : (term299 r) = (term300 r).
Proof. exact (MK_COMB (@lem4771923) (@lem4771922 r)). Qed.
Lemma lem4771925 (r : nat -> nat) (x : nat) : (term292 r x) = (term131 r x).
Proof. exact (eq_refl (term292 r x)). Qed.
Lemma lem4771926 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4771927 (r : nat -> nat) (x : nat) : (term301 r x) = (term302 r x).
Proof. exact (MK_COMB (@lem4771926) (@lem4771925 r x)). Qed.
Lemma lem4771928 (r : nat -> nat) (x : nat) : (term296 r x) = (term286 r x).
Proof. exact (eq_refl (term296 r x)). Qed.
Lemma lem4771929 (r : nat -> nat) (x : nat) : (term303 r x) = (term304 r x).
Proof. exact (MK_COMB (@lem4771927 r x) (@lem4771928 r x)). Qed.
Lemma lem4771930 (r : nat -> nat) : (term305 r) = (term306 r).
Proof. exact (fun_ext (fun x : nat => @lem4771929 r x)). Qed.
Lemma lem4771931 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771932 (r : nat -> nat) : (term291 r) = (term307 r).
Proof. exact (MK_COMB (@lem4771931) (@lem4771930 r)). Qed.
Lemma lem4771933 (r : nat -> nat) : ((term290 r) = (term291 r)) = ((term289 r) = (term307 r)).
Proof. exact (MK_COMB (@lem4771924 r) (@lem4771932 r)). Qed.
Lemma lem4771934 (r : nat -> nat) : (term289 r) = (term307 r).
Proof. exact (EQ_MP (@lem4771933 r) (@lem4771911 r)). Qed.
Lemma lem4771936 {A : Type'} (P : Prop) (Q : A -> Prop) : (term308 A P Q) = (term309 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4771937 (P : Prop) (Q : nat -> Prop) : (term310 P Q) = (term311 P Q).
Proof. exact (@lem4771936 nat P Q). Qed.
Lemma lem4771938 (r : nat -> nat) (x : nat) : (term312 r x) = (term313 r x).
Proof. exact (@lem4771937 (term131 r x) (term285 r x)). Qed.
Lemma lem4771939 (r : nat -> nat) (x : nat) (n : nat) : (term314 r x n) = (term283 r x n).
Proof. exact (eq_refl (term314 r x n)). Qed.
Lemma lem4771940 (r : nat -> nat) (x : nat) : (term315 r x) = (term285 r x).
Proof. exact (fun_ext (fun n : nat => @lem4771939 r x n)). Qed.
Lemma lem4771941 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771942 (r : nat -> nat) (x : nat) : (term316 r x) = (term286 r x).
Proof. exact (MK_COMB (@lem4771941) (@lem4771940 r x)). Qed.
Lemma lem4771943 (r : nat -> nat) (x : nat) : (term302 r x) = (term302 r x).
Proof. exact (eq_refl (term302 r x)). Qed.
Lemma lem4771944 (r : nat -> nat) (x : nat) : (term312 r x) = (term304 r x).
Proof. exact (MK_COMB (@lem4771943 r x) (@lem4771942 r x)). Qed.
Lemma lem4771945 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4771946 (r : nat -> nat) (x : nat) : (term317 r x) = (term318 r x).
Proof. exact (MK_COMB (@lem4771945) (@lem4771944 r x)). Qed.
Lemma lem4771947 (r : nat -> nat) (x : nat) (n : nat) : (term314 r x n) = (term283 r x n).
Proof. exact (eq_refl (term314 r x n)). Qed.
Lemma lem4771948 (r : nat -> nat) (x : nat) : (term302 r x) = (term302 r x).
Proof. exact (eq_refl (term302 r x)). Qed.
Lemma lem4771949 (r : nat -> nat) (x : nat) (n : nat) : (term319 r x n) = (term320 r x n).
Proof. exact (MK_COMB (@lem4771948 r x) (@lem4771947 r x n)). Qed.
Lemma lem4771950 (r : nat -> nat) (x : nat) : (term321 r x) = (term322 r x).
Proof. exact (fun_ext (fun n : nat => @lem4771949 r x n)). Qed.
Lemma lem4771951 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771952 (r : nat -> nat) (x : nat) : (term313 r x) = (term323 r x).
Proof. exact (MK_COMB (@lem4771951) (@lem4771950 r x)). Qed.
Lemma lem4771953 (r : nat -> nat) (x : nat) : ((term312 r x) = (term313 r x)) = ((term304 r x) = (term323 r x)).
Proof. exact (MK_COMB (@lem4771946 r x) (@lem4771952 r x)). Qed.
Lemma lem4771954 (r : nat -> nat) (x : nat) : (term304 r x) = (term323 r x).
Proof. exact (EQ_MP (@lem4771953 r x) (@lem4771938 r x)). Qed.
Lemma lem4771955 (r : nat -> nat) : (term306 r) = (term324 r).
Proof. exact (fun_ext (fun x : nat => @lem4771954 r x)). Qed.
Lemma lem4771956 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4771957 (r : nat -> nat) : (term307 r) = (term325 r).
Proof. exact (MK_COMB (@lem4771956) (@lem4771955 r)). Qed.
Lemma lem4771958 (r : nat -> nat) : (term289 r) = (term325 r).
Proof. exact (TRANS (@lem4771934 r) (@lem4771957 r)). Qed.
Lemma lem4771959 (r : nat -> nat) : (term246 r) = (term325 r).
Proof. exact (TRANS (@lem4771907 r) (@lem4771958 r)). Qed.
Lemma lem4771960 (r : nat -> nat) : (term197 r) = (term325 r).
Proof. exact (TRANS (@lem4771784 r) (@lem4771959 r)). Qed.
Lemma lem4771961 (r : nat -> nat) : (term94 r) = (term325 r).
Proof. exact (TRANS (@lem4771416 r) (@lem4771960 r)). Qed.
Lemma lem4771962 (r : nat -> nat) (h1 : term94 r) : term325 r.
Proof. exact (EQ_MP (@lem4771961 r) (@lem4771220 r h1)). Qed.
Lemma lem4771963 (n : nat) : (term118 n) = (term118 n).
Proof. exact (eq_refl (term118 n)). Qed.
Lemma lem4771964 : term119 = term119.
Proof. exact (fun_ext (fun n : nat => @lem4771963 n)). Qed.
Lemma lem4771965 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4771974 : term101 = term101.
Proof. exact (MK_COMB (@lem4771965) (@lem4771964)). Qed.
Lemma lem4771975 (h1 : term101) : term101.
Proof. exact (EQ_MP (@lem4771974) (@lem4771221 h1)). Qed.
Lemma lem4771976 (r : nat -> nat) (x : nat) (h1 : term323 r x) : term323 r x.
Proof. exact (h1). Qed.
Lemma lem4771977 (r : nat -> nat) (x : nat) (n : nat) (h1 : term320 r x n) : term320 r x n.
Proof. exact (h1). Qed.
Lemma lem4771978 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem4771983 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4771984 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem4771983 nat nat f x). Qed.
Lemma lem4771986 (r : nat -> nat) (m : nat) : (r m) = (@I (nat -> nat) r m).
Proof. exact (@lem4771984 r m). Qed.
Lemma lem4771991 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4771992 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem4771991 nat nat f x). Qed.
Lemma lem4771994 (r : nat -> nat) (n : nat) : (r n) = (@I (nat -> nat) r n).
Proof. exact (@lem4771992 r n). Qed.
Lemma lem4771995 (r : nat -> nat) (m : nat) : (term326 r m) = (term327 r m).
Proof. exact (MK_COMB (@lem4771978) (@lem4771986 r m)). Qed.
Lemma lem4771996 (m : nat) (r : nat -> nat) (n : nat) : (term125 m r n) = (term328 m r n).
Proof. exact (MK_COMB (@lem4771995 r m) (@lem4771994 r n)). Qed.
Lemma lem4772005 (m : nat) (n : nat) : (term329 m n) = (term329 m n).
Proof. exact (eq_refl (term329 m n)). Qed.
Lemma lem4772006 (m : nat) (r : nat -> nat) (n : nat) : (term124 m r n) = (term330 m r n).
Proof. exact (MK_COMB (@lem4772005 m n) (@lem4771996 m r n)). Qed.
Lemma lem4772007 (m : nat) (r : nat -> nat) : (term126 m r) = (term331 m r).
Proof. exact (fun_ext (fun n : nat => @lem4772006 m r n)). Qed.
Lemma lem4772008 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4772009 (m : nat) (r : nat -> nat) : (term127 m r) = (term332 m r).
Proof. exact (MK_COMB (@lem4772008) (@lem4772007 m r)). Qed.
Lemma lem4772010 (r : nat -> nat) : (term128 r) = (term333 r).
Proof. exact (fun_ext (fun m : nat => @lem4772009 m r)). Qed.
Lemma lem4772011 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4772012 (r : nat -> nat) : (term129 r) = (term334 r).
Proof. exact (MK_COMB (@lem4772011) (@lem4772010 r)). Qed.
Lemma lem4772013 (r : nat -> nat) (h1 : term21 r) : term334 r.
Proof. exact (EQ_MP (@lem4772012 r) (@lem4771291 r h1)). Qed.
Lemma lem4772030 (n : nat) : (term118 n) = (term118 n).
Proof. exact (eq_refl (term118 n)). Qed.
Lemma lem4772031 : term119 = term119.
Proof. exact (fun_ext (fun n : nat => @lem4772030 n)). Qed.
Lemma lem4772032 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4772033 : term101 = term101.
Proof. exact (MK_COMB (@lem4772032) (@lem4772031)). Qed.
Lemma lem4772034 (h1 : term101) : term101.
Proof. exact (EQ_MP (@lem4772033) (@lem4771975 h1)). Qed.
Lemma lem4772041 (x : nat) (n : nat) : (term335 x n) = (term335 x n).
Proof. exact (eq_refl (term335 x n)). Qed.
Lemma lem4772042 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4772047 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4772048 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem4772047 nat nat f x). Qed.
Lemma lem4772050 (r : nat -> nat) (x : nat) : (r x) = (@I (nat -> nat) r x).
Proof. exact (@lem4772048 r x). Qed.
Lemma lem4772055 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4772056 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem4772055 nat nat f x). Qed.
Lemma lem4772058 (r : nat -> nat) (n : nat) : (r n) = (@I (nat -> nat) r n).
Proof. exact (@lem4772056 r n). Qed.
Lemma lem4772059 (r : nat -> nat) (x : nat) : (term336 r x) = (term337 r x).
Proof. exact (MK_COMB (@lem4772042) (@lem4772050 r x)). Qed.
Lemma lem4772060 (x : nat) (r : nat -> nat) (n : nat) : ((r x) = (r n)) = ((@I (nat -> nat) r x) = (@I (nat -> nat) r n)).
Proof. exact (MK_COMB (@lem4772059 r x) (@lem4772058 r n)). Qed.
Lemma lem4772061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4772062 (x : nat) (r : nat -> nat) (n : nat) : (term338 x r n) = (term339 x r n).
Proof. exact (MK_COMB (@lem4772061) (@lem4772060 x r n)). Qed.
Lemma lem4772063 (r : nat -> nat) (x : nat) (n : nat) : (term142 r x n) = (term340 r x n).
Proof. exact (MK_COMB (@lem4772062 x r n) (@lem4772041 x n)). Qed.
Lemma lem4772070 (x : nat) (n : nat) : (term171 x n) = (term171 x n).
Proof. exact (eq_refl (term171 x n)). Qed.
Lemma lem4772071 (r : nat -> nat) (x : nat) (n : nat) : (term173 r x n) = (term341 r x n).
Proof. exact (MK_COMB (@lem4772070 x n) (@lem4772063 r x n)). Qed.
Lemma lem4772076 (n : nat) (x : nat) : (n = x) = (n = x).
Proof. exact (eq_refl (n = x)). Qed.
Lemma lem4772077 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4772078 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4772083 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4772084 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem4772083 nat nat f x). Qed.
Lemma lem4772086 (r : nat -> nat) (n : nat) : (r n) = (@I (nat -> nat) r n).
Proof. exact (@lem4772084 r n). Qed.
Lemma lem4772091 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4772092 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem4772091 nat nat f x). Qed.
Lemma lem4772094 (r : nat -> nat) (x : nat) : (r x) = (@I (nat -> nat) r x).
Proof. exact (@lem4772092 r x). Qed.
Lemma lem4772095 (r : nat -> nat) (n : nat) : (term336 r n) = (term337 r n).
Proof. exact (MK_COMB (@lem4772078) (@lem4772086 r n)). Qed.
Lemma lem4772096 (n : nat) (r : nat -> nat) (x : nat) : ((r n) = (r x)) = ((@I (nat -> nat) r n) = (@I (nat -> nat) r x)).
Proof. exact (MK_COMB (@lem4772095 r n) (@lem4772094 r x)). Qed.
Lemma lem4772097 (n : nat) (r : nat -> nat) (x : nat) : (term342 n r x) = (term343 n r x).
Proof. exact (MK_COMB (@lem4772077) (@lem4772096 n r x)). Qed.
Lemma lem4772098 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4772099 (n : nat) (r : nat -> nat) (x : nat) : (term344 n r x) = (term345 n r x).
Proof. exact (MK_COMB (@lem4772098) (@lem4772097 n r x)). Qed.
Lemma lem4772100 (r : nat -> nat) (n : nat) (x : nat) : (term143 r n x) = (term346 r n x).
Proof. exact (MK_COMB (@lem4772099 n r x) (@lem4772076 n x)). Qed.
Lemma lem4772107 (x : nat) (n : nat) : (term335 x n) = (term335 x n).
Proof. exact (eq_refl (term335 x n)). Qed.
Lemma lem4772108 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4772113 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4772114 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem4772113 nat nat f x). Qed.
Lemma lem4772116 (r : nat -> nat) (x : nat) : (r x) = (@I (nat -> nat) r x).
Proof. exact (@lem4772114 r x). Qed.
Lemma lem4772121 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4772122 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem4772121 nat nat f x). Qed.
Lemma lem4772124 (r : nat -> nat) (n : nat) : (r n) = (@I (nat -> nat) r n).
Proof. exact (@lem4772122 r n). Qed.
Lemma lem4772125 (r : nat -> nat) (x : nat) : (term336 r x) = (term337 r x).
Proof. exact (MK_COMB (@lem4772108) (@lem4772116 r x)). Qed.
Lemma lem4772126 (x : nat) (r : nat -> nat) (n : nat) : ((r x) = (r n)) = ((@I (nat -> nat) r x) = (@I (nat -> nat) r n)).
Proof. exact (MK_COMB (@lem4772125 r x) (@lem4772124 r n)). Qed.
Lemma lem4772127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4772128 (x : nat) (r : nat -> nat) (n : nat) : (term338 x r n) = (term339 x r n).
Proof. exact (MK_COMB (@lem4772127) (@lem4772126 x r n)). Qed.
Lemma lem4772129 (r : nat -> nat) (x : nat) (n : nat) : (term142 r x n) = (term340 r x n).
Proof. exact (MK_COMB (@lem4772128 x r n) (@lem4772107 x n)). Qed.
Lemma lem4772130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4772131 (r : nat -> nat) (x : nat) (n : nat) : (term145 r x n) = (term347 r x n).
Proof. exact (MK_COMB (@lem4772130) (@lem4772129 r x n)). Qed.
Lemma lem4772132 (r : nat -> nat) (n : nat) (x : nat) : (term147 r n x) = (term348 r n x).
Proof. exact (MK_COMB (@lem4772131 r x n) (@lem4772100 r n x)). Qed.
Lemma lem4772139 (n : nat) (x : nat) : (term335 n x) = (term335 n x).
Proof. exact (eq_refl (term335 n x)). Qed.
Lemma lem4772140 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4772145 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4772146 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem4772145 nat nat f x). Qed.
Lemma lem4772148 (r : nat -> nat) (n : nat) : (r n) = (@I (nat -> nat) r n).
Proof. exact (@lem4772146 r n). Qed.
Lemma lem4772153 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4772154 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem4772153 nat nat f x). Qed.
Lemma lem4772156 (r : nat -> nat) (x : nat) : (r x) = (@I (nat -> nat) r x).
Proof. exact (@lem4772154 r x). Qed.
Lemma lem4772157 (r : nat -> nat) (n : nat) : (term336 r n) = (term337 r n).
Proof. exact (MK_COMB (@lem4772140) (@lem4772148 r n)). Qed.
Lemma lem4772158 (n : nat) (r : nat -> nat) (x : nat) : ((r n) = (r x)) = ((@I (nat -> nat) r n) = (@I (nat -> nat) r x)).
Proof. exact (MK_COMB (@lem4772157 r n) (@lem4772156 r x)). Qed.
Lemma lem4772159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4772160 (n : nat) (r : nat -> nat) (x : nat) : (term338 n r x) = (term339 n r x).
Proof. exact (MK_COMB (@lem4772159) (@lem4772158 n r x)). Qed.
Lemma lem4772161 (r : nat -> nat) (n : nat) (x : nat) : (term142 r n x) = (term340 r n x).
Proof. exact (MK_COMB (@lem4772160 n r x) (@lem4772139 n x)). Qed.
Lemma lem4772166 (x : nat) (n : nat) : (x = n) = (x = n).
Proof. exact (eq_refl (x = n)). Qed.
Lemma lem4772167 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4772168 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4772173 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4772174 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem4772173 nat nat f x). Qed.
Lemma lem4772176 (r : nat -> nat) (x : nat) : (r x) = (@I (nat -> nat) r x).
Proof. exact (@lem4772174 r x). Qed.
Lemma lem4772181 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4772182 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem4772181 nat nat f x). Qed.
Lemma lem4772184 (r : nat -> nat) (n : nat) : (r n) = (@I (nat -> nat) r n).
Proof. exact (@lem4772182 r n). Qed.
Lemma lem4772185 (r : nat -> nat) (x : nat) : (term336 r x) = (term337 r x).
Proof. exact (MK_COMB (@lem4772168) (@lem4772176 r x)). Qed.
Lemma lem4772186 (x : nat) (r : nat -> nat) (n : nat) : ((r x) = (r n)) = ((@I (nat -> nat) r x) = (@I (nat -> nat) r n)).
Proof. exact (MK_COMB (@lem4772185 r x) (@lem4772184 r n)). Qed.
Lemma lem4772187 (x : nat) (r : nat -> nat) (n : nat) : (term342 x r n) = (term343 x r n).
Proof. exact (MK_COMB (@lem4772167) (@lem4772186 x r n)). Qed.
Lemma lem4772188 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4772189 (x : nat) (r : nat -> nat) (n : nat) : (term344 x r n) = (term345 x r n).
Proof. exact (MK_COMB (@lem4772188) (@lem4772187 x r n)). Qed.
Lemma lem4772190 (r : nat -> nat) (x : nat) (n : nat) : (term143 r x n) = (term346 r x n).
Proof. exact (MK_COMB (@lem4772189 x r n) (@lem4772166 x n)). Qed.
Lemma lem4772191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4772192 (r : nat -> nat) (x : nat) (n : nat) : (term149 r x n) = (term349 r x n).
Proof. exact (MK_COMB (@lem4772191) (@lem4772190 r x n)). Qed.
Lemma lem4772193 (r : nat -> nat) (n : nat) (x : nat) : (term151 r n x) = (term350 r n x).
Proof. exact (MK_COMB (@lem4772192 r x n) (@lem4772161 r n x)). Qed.
Lemma lem4772194 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4772195 (r : nat -> nat) (n : nat) (x : nat) : (term153 r n x) = (term351 r n x).
Proof. exact (MK_COMB (@lem4772194) (@lem4772193 r n x)). Qed.
Lemma lem4772196 (r : nat -> nat) (n : nat) (x : nat) : (term155 r n x) = (term352 r n x).
Proof. exact (MK_COMB (@lem4772195 r n x) (@lem4772132 r n x)). Qed.
Lemma lem4772197 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4772198 (r : nat -> nat) (n : nat) (x : nat) : (term281 r n x) = (term353 r n x).
Proof. exact (MK_COMB (@lem4772197) (@lem4772196 r n x)). Qed.
Lemma lem4772199 (r : nat -> nat) (x : nat) (n : nat) : (term283 r x n) = (term354 r x n).
Proof. exact (MK_COMB (@lem4772198 r n x) (@lem4772071 r x n)). Qed.
Lemma lem4772206 (x : nat) : (term355 x) = (term355 x).
Proof. exact (eq_refl (term355 x)). Qed.
Lemma lem4772207 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4772212 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4772213 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem4772212 nat nat f x). Qed.
Lemma lem4772215 (r : nat -> nat) (x : nat) : (r x) = (@I (nat -> nat) r x).
Proof. exact (@lem4772213 r x). Qed.
Lemma lem4772220 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4772221 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem4772220 nat nat f x). Qed.
Lemma lem4772223 (r : nat -> nat) (x : nat) : (r x) = (@I (nat -> nat) r x).
Proof. exact (@lem4772221 r x). Qed.
Lemma lem4772224 (r : nat -> nat) (x : nat) : (term336 r x) = (term337 r x).
Proof. exact (MK_COMB (@lem4772207) (@lem4772215 r x)). Qed.
Lemma lem4772225 (r : nat -> nat) (x : nat) : ((r x) = (r x)) = ((@I (nat -> nat) r x) = (@I (nat -> nat) r x)).
Proof. exact (MK_COMB (@lem4772224 r x) (@lem4772223 r x)). Qed.
Lemma lem4772226 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4772227 (r : nat -> nat) (x : nat) : (term356 r x) = (term357 r x).
Proof. exact (MK_COMB (@lem4772226) (@lem4772225 r x)). Qed.
Lemma lem4772228 (r : nat -> nat) (x : nat) : (term131 r x) = (term358 r x).
Proof. exact (MK_COMB (@lem4772227 r x) (@lem4772206 x)). Qed.
Lemma lem4772229 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4772230 (r : nat -> nat) (x : nat) : (term302 r x) = (term359 r x).
Proof. exact (MK_COMB (@lem4772229) (@lem4772228 r x)). Qed.
Lemma lem4772231 (r : nat -> nat) (x : nat) (n : nat) : (term320 r x n) = (term360 r x n).
Proof. exact (MK_COMB (@lem4772230 r x) (@lem4772199 r x n)). Qed.
Lemma lem4772232 (r : nat -> nat) (x : nat) (n : nat) (h1 : term320 r x n) : term360 r x n.
Proof. exact (EQ_MP (@lem4772231 r x n) (@lem4771977 r x n h1)). Qed.
Lemma lem4772233 (r : nat -> nat) (x : nat) (h1 : term358 r x) : term358 r x.
Proof. exact (h1). Qed.
Lemma lem4772234 (r : nat -> nat) (x : nat) (n : nat) (h1 : term354 r x n) : term354 r x n.
Proof. exact (h1). Qed.
Lemma lem4772237 (r : nat -> nat) (n : nat) (x : nat) (h1 : term352 r n x) : term352 r n x.
Proof. exact (h1). Qed.
Lemma lem4772238 (r : nat -> nat) (x : nat) (n : nat) (h1 : term341 r x n) : term341 r x n.
Proof. exact (h1). Qed.
Lemma lem4772239 (r : nat -> nat) (n : nat) (x : nat) (h1 : term350 r n x) : term350 r n x.
Proof. exact (h1). Qed.
Lemma lem4772240 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) : term348 r n x.
Proof. exact (h1). Qed.
Lemma lem4772241 (r : nat -> nat) (n : nat) (x : nat) (h1 : term350 r n x) : term340 r n x.
Proof. exact (proj2 (@lem4772239 r n x h1)). Qed.
Lemma lem4772242 (r : nat -> nat) (n : nat) (x : nat) (h1 : term350 r n x) : term346 r x n.
Proof. exact (proj1 (@lem4772239 r n x h1)). Qed.
Lemma lem4772247 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) : term346 r n x.
Proof. exact (proj2 (@lem4772240 r n x h1)). Qed.
Lemma lem4772248 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) : term340 r x n.
Proof. exact (proj1 (@lem4772240 r n x h1)). Qed.
Lemma lem4772253 (r : nat -> nat) (x : nat) (n : nat) (h1 : term341 r x n) : term340 r x n.
Proof. exact (proj2 (@lem4772238 r x n h1)). Qed.
Lemma lem4772330 (x : nat) (r : nat -> nat) (n : nat) (h1 : term343 x r n) : term343 x r n.
Proof. exact (h1). Qed.
Lemma lem4772369 (x : nat) (n : nat) (h1 : x = n) : x = n.
Proof. exact (h1). Qed.
Lemma lem4772408 (n : nat) (r : nat -> nat) (x : nat) (h1 : term343 n r x) : term343 n r x.
Proof. exact (h1). Qed.
Lemma lem4772447 (n : nat) (x : nat) (h1 : n = x) : n = x.
Proof. exact (h1). Qed.
Lemma lem4772455 (m : nat) (r : nat -> nat) (n : nat) : (term330 m r n) = (term330 m r n).
Proof. exact (eq_refl (term330 m r n)). Qed.
Lemma lem4772456 (m : nat) (r : nat -> nat) : (term331 m r) = (term331 m r).
Proof. exact (fun_ext (fun n : nat => @lem4772455 m r n)). Qed.
Lemma lem4772457 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4772458 (m : nat) (r : nat -> nat) : (term332 m r) = (term332 m r).
Proof. exact (MK_COMB (@lem4772457) (@lem4772456 m r)). Qed.
Lemma lem4772459 (r : nat -> nat) : (term333 r) = (term333 r).
Proof. exact (fun_ext (fun m : nat => @lem4772458 m r)). Qed.
Lemma lem4772460 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4772462 (r : nat -> nat) : (term334 r) = (term334 r).
Proof. exact (MK_COMB (@lem4772460) (@lem4772459 r)). Qed.
Lemma lem4772463 (r : nat -> nat) (h1 : term21 r) : term334 r.
Proof. exact (EQ_MP (@lem4772462 r) (@lem4772013 r h1)). Qed.
Lemma lem4772469 (n : nat) : (term118 n) = (term118 n).
Proof. exact (eq_refl (term118 n)). Qed.
Lemma lem4772470 : term119 = term119.
Proof. exact (fun_ext (fun n : nat => @lem4772469 n)). Qed.
Lemma lem4772471 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4772473 : term101 = term101.
Proof. exact (MK_COMB (@lem4772471) (@lem4772470)). Qed.
Lemma lem4772474 (h1 : term101) : term101.
Proof. exact (EQ_MP (@lem4772473) (@lem4772034 h1)). Qed.
Lemma lem4772532 (_58757 : nat) (r : nat -> nat) (h1 : term21 r) : term361 r _58757.
Proof. exact (@lem4772463 r h1 _58757). Qed.
Lemma lem4772533 (_58757 : nat) (r : nat -> nat) : (term361 r _58757) = (term332 _58757 r).
Proof. exact (eq_refl (term361 r _58757)). Qed.
Lemma lem4772534 (_58757 : nat) (r : nat -> nat) (h1 : term21 r) : term332 _58757 r.
Proof. exact (EQ_MP (@lem4772533 _58757 r) (@lem4772532 _58757 r h1)). Qed.
Lemma lem4772535 (_58757 : nat) (_58758 : nat) (r : nat -> nat) (h1 : term21 r) : term362 _58757 r _58758.
Proof. exact (@lem4772534 _58757 r h1 _58758). Qed.
Lemma lem4772536 (_58757 : nat) (r : nat -> nat) (_58758 : nat) : (term362 _58757 r _58758) = (term330 _58757 r _58758).
Proof. exact (eq_refl (term362 _58757 r _58758)). Qed.
Lemma lem4772538 (_58759 : nat) (h1 : term101) : term363 _58759.
Proof. exact (@lem4772474 h1 _58759). Qed.
Lemma lem4772539 (_58759 : nat) : (term363 _58759) = (term118 _58759).
Proof. exact (eq_refl (term363 _58759)). Qed.
Lemma lem4772570 (x : nat) (r : nat -> nat) (n : nat) (h1 : term343 x r n) : term343 x r n.
Proof. exact (h1). Qed.
Lemma lem4772584 (r : nat -> nat) (n : nat) (x : nat) (h1 : term350 r n x) : term335 n x.
Proof. exact (proj2 (@lem4772241 r n x h1)). Qed.
Lemma lem4772586 (x : nat) (n : nat) (h1 : x = n) : x = n.
Proof. exact (h1). Qed.
Lemma lem4772602 (n : nat) (r : nat -> nat) (x : nat) (h1 : term343 n r x) : term343 n r x.
Proof. exact (h1). Qed.
Lemma lem4772616 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) : term335 x n.
Proof. exact (proj2 (@lem4772248 r n x h1)). Qed.
Lemma lem4772618 (n : nat) (x : nat) (h1 : n = x) : n = x.
Proof. exact (h1). Qed.
Lemma lem4772690 (r : nat -> nat) (x : nat) (h1 : term358 r x) : term355 x.
Proof. exact (proj2 (@lem4772233 r x h1)). Qed.
Lemma lem4772774 (x : nat) (r : nat -> nat) (n : nat) (h1 : term343 x r n) : term343 x r n.
Proof. exact (h1). Qed.
Lemma lem4772844 (n : nat) : (term364 n) = (term364 n).
Proof. exact (eq_refl (term364 n)). Qed.
Lemma lem4772845 (x : nat) (n : nat) (h1 : x = n) : (term365 n x) = (term366 n).
Proof. exact (MK_COMB (@lem4772844 n) (@lem4772586 x n h1)). Qed.
Lemma lem4772846 (n : nat) : (term366 n) = (term355 n).
Proof. exact (eq_refl (term366 n)). Qed.
Lemma lem4772847 (n : nat) (x : nat) : (term367 n x) = (term367 n x).
Proof. exact (eq_refl (term367 n x)). Qed.
Lemma lem4772848 (x : nat) (n : nat) : ((term365 n x) = (term366 n)) = ((term365 n x) = (term355 n)).
Proof. exact (MK_COMB (@lem4772847 n x) (@lem4772846 n)). Qed.
Lemma lem4772849 (n : nat) (x : nat) : (term365 n x) = (term335 n x).
Proof. exact (eq_refl (term365 n x)). Qed.
Lemma lem4772850 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4772851 (n : nat) (x : nat) : (term367 n x) = (term368 n x).
Proof. exact (MK_COMB (@lem4772850) (@lem4772849 n x)). Qed.
Lemma lem4772852 (n : nat) : (term355 n) = (term355 n).
Proof. exact (eq_refl (term355 n)). Qed.
Lemma lem4772853 (x : nat) (n : nat) : ((term365 n x) = (term355 n)) = ((term335 n x) = (term355 n)).
Proof. exact (MK_COMB (@lem4772851 n x) (@lem4772852 n)). Qed.
Lemma lem4772854 (x : nat) (n : nat) : ((term365 n x) = (term366 n)) = ((term335 n x) = (term355 n)).
Proof. exact (TRANS (@lem4772848 x n) (@lem4772853 x n)). Qed.
Lemma lem4772855 (x : nat) (n : nat) (h1 : x = n) : (term335 n x) = (term355 n).
Proof. exact (EQ_MP (@lem4772854 x n) (@lem4772845 x n h1)). Qed.
Lemma lem4772912 (r : nat -> nat) (x : nat) (n : nat) (h1 : term350 r n x) (h2 : x = n) : term355 n.
Proof. exact (EQ_MP (@lem4772855 x n h2) (@lem4772584 r n x h1)). Qed.
Lemma lem4772996 (n : nat) (r : nat -> nat) (x : nat) (h1 : term343 n r x) : term343 n r x.
Proof. exact (h1). Qed.
Lemma lem4773066 (x : nat) : (term364 x) = (term364 x).
Proof. exact (eq_refl (term364 x)). Qed.
Lemma lem4773067 (n : nat) (x : nat) (h1 : n = x) : (term365 x n) = (term366 x).
Proof. exact (MK_COMB (@lem4773066 x) (@lem4772618 n x h1)). Qed.
Lemma lem4773068 (x : nat) : (term366 x) = (term355 x).
Proof. exact (eq_refl (term366 x)). Qed.
Lemma lem4773069 (x : nat) (n : nat) : (term367 x n) = (term367 x n).
Proof. exact (eq_refl (term367 x n)). Qed.
Lemma lem4773070 (n : nat) (x : nat) : ((term365 x n) = (term366 x)) = ((term365 x n) = (term355 x)).
Proof. exact (MK_COMB (@lem4773069 x n) (@lem4773068 x)). Qed.
Lemma lem4773071 (x : nat) (n : nat) : (term365 x n) = (term335 x n).
Proof. exact (eq_refl (term365 x n)). Qed.
Lemma lem4773072 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4773073 (x : nat) (n : nat) : (term367 x n) = (term368 x n).
Proof. exact (MK_COMB (@lem4773072) (@lem4773071 x n)). Qed.
Lemma lem4773074 (x : nat) : (term355 x) = (term355 x).
Proof. exact (eq_refl (term355 x)). Qed.
Lemma lem4773075 (n : nat) (x : nat) : ((term365 x n) = (term355 x)) = ((term335 x n) = (term355 x)).
Proof. exact (MK_COMB (@lem4773073 x n) (@lem4773074 x)). Qed.
Lemma lem4773076 (n : nat) (x : nat) : ((term365 x n) = (term366 x)) = ((term335 x n) = (term355 x)).
Proof. exact (TRANS (@lem4773070 n x) (@lem4773075 n x)). Qed.
Lemma lem4773077 (n : nat) (x : nat) (h1 : n = x) : (term335 x n) = (term355 x).
Proof. exact (EQ_MP (@lem4773076 n x) (@lem4773067 n x h1)). Qed.
Lemma lem4773134 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) (h2 : n = x) : term355 x.
Proof. exact (EQ_MP (@lem4773077 n x h2) (@lem4772616 r n x h1)). Qed.
Lemma lem4773162 (_58757 : nat) (_58758 : nat) (r : nat -> nat) (h1 : term21 r) : term330 _58757 r _58758.
Proof. exact (EQ_MP (@lem4772536 _58757 r _58758) (@lem4772535 _58757 _58758 r h1)). Qed.
Lemma lem4773176 (_58759 : nat) (h1 : term101) : term118 _58759.
Proof. exact (EQ_MP (@lem4772539 _58759) (@lem4772538 _58759 h1)). Qed.
Lemma lem4773258 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4773259 (x : nat) : term369 x.
Proof. exact (fun h0 : term355 x => @lem4773258 x). Qed.
Lemma lem4773261 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4773262 (x : nat) : (term369 x) = (x = x).
Proof. exact (@lem4773261 (x = x)). Qed.
Lemma lem4773263 (x : nat) : x = x.
Proof. exact (EQ_MP (@lem4773262 x) (@lem4773259 x)). Qed.
Lemma lem4773266 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4773268 (x : nat) : (term355 x) = (term371 x).
Proof. exact (@lem4773266 (x = x)). Qed.
Lemma lem4773271 (r : nat -> nat) (x : nat) (h1 : term358 r x) : term371 x.
Proof. exact (EQ_MP (@lem4773268 x) (@lem4772690 r x h1)). Qed.
Lemma lem4773274 (r : nat -> nat) (x : nat) (h1 : term358 r x) : False.
Proof. exact (@lem4773271 r x h1 (@lem4773263 x)). Qed.
Lemma lem4773275 (r : nat -> nat) (x : nat) (h1 : term358 r x) : term372.
Proof. exact (fun h0 : ~ False => @lem4773274 r x h1). Qed.
Lemma lem4773277 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4773278 : term372 = False.
Proof. exact (@lem4773277 False). Qed.
Lemma lem4773315 (x : nat) (y : nat) (z : nat) : term373 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem4773319 (r : nat -> nat) (n : nat) (x : nat) (h1 : term350 r n x) : (@I (nat -> nat) r n) = (@I (nat -> nat) r x).
Proof. exact (proj1 (@lem4772241 r n x h1)). Qed.
Lemma lem4773320 (r : nat -> nat) (n : nat) (x : nat) (h1 : term350 r n x) : term374 n r x.
Proof. exact (fun h0 : term343 n r x => @lem4773319 r n x h1). Qed.
Lemma lem4773322 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4773323 (n : nat) (r : nat -> nat) (x : nat) : (term374 n r x) = ((@I (nat -> nat) r n) = (@I (nat -> nat) r x)).
Proof. exact (@lem4773322 ((@I (nat -> nat) r n) = (@I (nat -> nat) r x))). Qed.
Lemma lem4773324 (r : nat -> nat) (n : nat) (x : nat) (h1 : term350 r n x) : (@I (nat -> nat) r n) = (@I (nat -> nat) r x).
Proof. exact (EQ_MP (@lem4773323 n r x) (@lem4773320 r n x h1)). Qed.
Lemma lem4773326 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4773327 (r : nat -> nat) (n : nat) : (@I (nat -> nat) r n) = (@I (nat -> nat) r n).
Proof. exact (@lem4773326 (@I (nat -> nat) r n)). Qed.
Lemma lem4773328 (r : nat -> nat) (n : nat) : term375 r n.
Proof. exact (fun h0 : term376 r n => @lem4773327 r n). Qed.
Lemma lem4773330 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4773331 (r : nat -> nat) (n : nat) : (term375 r n) = ((@I (nat -> nat) r n) = (@I (nat -> nat) r n)).
Proof. exact (@lem4773330 ((@I (nat -> nat) r n) = (@I (nat -> nat) r n))). Qed.
Lemma lem4773332 (r : nat -> nat) (n : nat) : (@I (nat -> nat) r n) = (@I (nat -> nat) r n).
Proof. exact (EQ_MP (@lem4773331 r n) (@lem4773328 r n)). Qed.
Lemma lem4773350 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4773351 (y : nat) (x : nat) (z : nat) : (term377 x y z) = (term378 y x z).
Proof. exact (@lem4773350 (y = z) (term335 x z)). Qed.
Lemma lem4773361 (x : nat) (y : nat) : (term379 x y) = (term379 x y).
Proof. exact (eq_refl (term379 x y)). Qed.
Lemma lem4773362 (y : nat) (x : nat) (z : nat) : (term373 x y z) = (term380 y x z).
Proof. exact (MK_COMB (@lem4773361 x y) (@lem4773351 y x z)). Qed.
Lemma lem4773366 (q : Prop) (p : Prop) (r : Prop) : (term381 p q r) = (term381 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4773367 (y : nat) (x : nat) (z : nat) : (term380 y x z) = (term382 y x z).
Proof. exact (@lem4773366 (y = z) (term335 x y) (term335 x z)). Qed.
Lemma lem4773389 (y : nat) (x : nat) (z : nat) : (term373 x y z) = (term382 y x z).
Proof. exact (TRANS (@lem4773362 y x z) (@lem4773367 y x z)). Qed.
Lemma lem4773390 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4773391 (y : nat) (x : nat) (z : nat) : (term383 x y z) = (term384 y x z).
Proof. exact (MK_COMB (@lem4773390) (@lem4773389 y x z)). Qed.
Lemma lem4773413 (y : nat) (x : nat) (z : nat) : (term382 y x z) = (term382 y x z).
Proof. exact (eq_refl (term382 y x z)). Qed.
Lemma lem4773414 (y : nat) (x : nat) (z : nat) : ((term373 x y z) = (term382 y x z)) = ((term382 y x z) = (term382 y x z)).
Proof. exact (MK_COMB (@lem4773391 y x z) (@lem4773413 y x z)). Qed.
Lemma lem4773416 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4773417 (x : Prop) : (x = x) = True.
Proof. exact (@lem4773416 Prop x). Qed.
Lemma lem4773418 (y : nat) (x : nat) (z : nat) : ((term382 y x z) = (term382 y x z)) = True.
Proof. exact (@lem4773417 (term382 y x z)). Qed.
Lemma lem4773419 (y : nat) (x : nat) (z : nat) : ((term373 x y z) = (term382 y x z)) = True.
Proof. exact (TRANS (@lem4773414 y x z) (@lem4773418 y x z)). Qed.
Lemma lem4773420 (y : nat) (x : nat) (z : nat) : True = ((term373 x y z) = (term382 y x z)).
Proof. exact (SYM (@lem4773419 y x z)). Qed.
Lemma lem4773421 (y : nat) (x : nat) (z : nat) : (term373 x y z) = (term382 y x z).
Proof. exact (EQ_MP (@lem4773420 y x z) (@lem0)). Qed.
Lemma lem4773422 (y : nat) (x : nat) (z : nat) : term382 y x z.
Proof. exact (EQ_MP (@lem4773421 y x z) (@lem4773315 x y z)). Qed.
Lemma lem4773424 (b : Prop) (a : Prop) : (a \/ b) = (term385 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4773425 (x : nat) (y : nat) (z : nat) : (term382 y x z) = (term386 x y z).
Proof. exact (@lem4773424 (term387 y x z) (y = z)). Qed.
Lemma lem4773427 (a : Prop) (b : Prop) : (term388 a b) = (term389 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4773428 (y : nat) (x : nat) (z : nat) : (term390 y x z) = (term391 y x z).
Proof. exact (@lem4773427 (term335 x y) (term335 x z)). Qed.
Lemma lem4773430 (a : Prop) : (term392 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4773431 (x : nat) (y : nat) : (term393 x y) = (x = y).
Proof. exact (@lem4773430 (x = y)). Qed.
Lemma lem4773432 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4773433 (x : nat) (y : nat) : (term394 x y) = (term395 x y).
Proof. exact (MK_COMB (@lem4773432) (@lem4773431 x y)). Qed.
Lemma lem4773435 (a : Prop) : (term392 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4773436 (x : nat) (z : nat) : (term393 x z) = (x = z).
Proof. exact (@lem4773435 (x = z)). Qed.
Lemma lem4773437 (y : nat) (x : nat) (z : nat) : (term391 y x z) = (term396 y x z).
Proof. exact (MK_COMB (@lem4773433 x y) (@lem4773436 x z)). Qed.
Lemma lem4773438 (y : nat) (x : nat) (z : nat) : (term390 y x z) = (term396 y x z).
Proof. exact (TRANS (@lem4773428 y x z) (@lem4773437 y x z)). Qed.
Lemma lem4773439 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4773440 (y : nat) (x : nat) (z : nat) : (term397 y x z) = (term398 y x z).
Proof. exact (MK_COMB (@lem4773439) (@lem4773438 y x z)). Qed.
Lemma lem4773441 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem4773442 (x : nat) (y : nat) (z : nat) : (term386 x y z) = (term399 x y z).
Proof. exact (MK_COMB (@lem4773440 y x z) (@lem4773441 y z)). Qed.
Lemma lem4773443 (x : nat) (y : nat) (z : nat) : (term382 y x z) = (term399 x y z).
Proof. exact (TRANS (@lem4773425 x y z) (@lem4773442 x y z)). Qed.
Lemma lem4773445 (r : nat -> nat) (n : nat) (x : nat) (h1 : term350 r n x) : term400 x r n.
Proof. exact (conj (@lem4773324 r n x h1) (@lem4773332 r n)). Qed.
Lemma lem4773447 (x : nat) (y : nat) (z : nat) : term399 x y z.
Proof. exact (EQ_MP (@lem4773443 x y z) (@lem4773422 y x z)). Qed.
Lemma lem4773448 (x : nat) (r : nat -> nat) (n : nat) : term401 x r n.
Proof. exact (@lem4773447 (@I (nat -> nat) r n) (@I (nat -> nat) r x) (@I (nat -> nat) r n)). Qed.
Lemma lem4773451 (r : nat -> nat) (n : nat) (x : nat) (h1 : term350 r n x) : (@I (nat -> nat) r x) = (@I (nat -> nat) r n).
Proof. exact (@lem4773448 x r n (@lem4773445 r n x h1)). Qed.
Lemma lem4773452 (r : nat -> nat) (n : nat) (x : nat) (h1 : term350 r n x) : term374 x r n.
Proof. exact (fun h0 : term343 x r n => @lem4773451 r n x h1). Qed.
Lemma lem4773454 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4773455 (x : nat) (r : nat -> nat) (n : nat) : (term374 x r n) = ((@I (nat -> nat) r x) = (@I (nat -> nat) r n)).
Proof. exact (@lem4773454 ((@I (nat -> nat) r x) = (@I (nat -> nat) r n))). Qed.
Lemma lem4773456 (r : nat -> nat) (n : nat) (x : nat) (h1 : term350 r n x) : (@I (nat -> nat) r x) = (@I (nat -> nat) r n).
Proof. exact (EQ_MP (@lem4773455 x r n) (@lem4773452 r n x h1)). Qed.
Lemma lem4773459 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4773461 (x : nat) (r : nat -> nat) (n : nat) : (term343 x r n) = (term402 x r n).
Proof. exact (@lem4773459 ((@I (nat -> nat) r x) = (@I (nat -> nat) r n))). Qed.
Lemma lem4773464 (x : nat) (r : nat -> nat) (n : nat) (h1 : term343 x r n) : term402 x r n.
Proof. exact (EQ_MP (@lem4773461 x r n) (@lem4772774 x r n h1)). Qed.
Lemma lem4773467 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 x r n) (h2 : term350 r n x) : False.
Proof. exact (@lem4773464 x r n h1 (@lem4773456 r n x h2)). Qed.
Lemma lem4773468 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 x r n) (h2 : term350 r n x) : term372.
Proof. exact (fun h0 : ~ False => @lem4773467 r n x h1 h2). Qed.
Lemma lem4773470 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4773471 : term372 = False.
Proof. exact (@lem4773470 False). Qed.
Lemma lem4773472 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 x r n) (h2 : term350 r n x) : False.
Proof. exact (EQ_MP (@lem4773471) (@lem4773468 r n x h1 h2)). Qed.
Lemma lem4773512 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4773513 (n : nat) : n = n.
Proof. exact (@lem4773512 n). Qed.
Lemma lem4773514 (n : nat) : term369 n.
Proof. exact (fun h0 : term355 n => @lem4773513 n). Qed.
Lemma lem4773516 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4773517 (n : nat) : (term369 n) = (n = n).
Proof. exact (@lem4773516 (n = n)). Qed.
Lemma lem4773518 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem4773517 n) (@lem4773514 n)). Qed.
Lemma lem4773521 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4773523 (n : nat) : (term355 n) = (term371 n).
Proof. exact (@lem4773521 (n = n)). Qed.
Lemma lem4773526 (r : nat -> nat) (x : nat) (n : nat) (h1 : term350 r n x) (h2 : x = n) : term371 n.
Proof. exact (EQ_MP (@lem4773523 n) (@lem4772912 r x n h1 h2)). Qed.
Lemma lem4773529 (r : nat -> nat) (x : nat) (n : nat) (h1 : term350 r n x) (h2 : x = n) : False.
Proof. exact (@lem4773526 r x n h1 h2 (@lem4773518 n)). Qed.
Lemma lem4773530 (r : nat -> nat) (x : nat) (n : nat) (h1 : term350 r n x) (h2 : x = n) : term372.
Proof. exact (fun h0 : ~ False => @lem4773529 r x n h1 h2). Qed.
Lemma lem4773532 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4773533 : term372 = False.
Proof. exact (@lem4773532 False). Qed.
Lemma lem4773570 (x : nat) (y : nat) (z : nat) : term373 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem4773574 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) : (@I (nat -> nat) r x) = (@I (nat -> nat) r n).
Proof. exact (proj1 (@lem4772248 r n x h1)). Qed.
Lemma lem4773575 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) : term374 x r n.
Proof. exact (fun h0 : term343 x r n => @lem4773574 r n x h1). Qed.
Lemma lem4773577 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4773578 (x : nat) (r : nat -> nat) (n : nat) : (term374 x r n) = ((@I (nat -> nat) r x) = (@I (nat -> nat) r n)).
Proof. exact (@lem4773577 ((@I (nat -> nat) r x) = (@I (nat -> nat) r n))). Qed.
Lemma lem4773579 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) : (@I (nat -> nat) r x) = (@I (nat -> nat) r n).
Proof. exact (EQ_MP (@lem4773578 x r n) (@lem4773575 r n x h1)). Qed.
Lemma lem4773581 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4773582 (r : nat -> nat) (x : nat) : (@I (nat -> nat) r x) = (@I (nat -> nat) r x).
Proof. exact (@lem4773581 (@I (nat -> nat) r x)). Qed.
Lemma lem4773583 (r : nat -> nat) (x : nat) : term375 r x.
Proof. exact (fun h0 : term376 r x => @lem4773582 r x). Qed.
Lemma lem4773585 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4773586 (r : nat -> nat) (x : nat) : (term375 r x) = ((@I (nat -> nat) r x) = (@I (nat -> nat) r x)).
Proof. exact (@lem4773585 ((@I (nat -> nat) r x) = (@I (nat -> nat) r x))). Qed.
Lemma lem4773587 (r : nat -> nat) (x : nat) : (@I (nat -> nat) r x) = (@I (nat -> nat) r x).
Proof. exact (EQ_MP (@lem4773586 r x) (@lem4773583 r x)). Qed.
Lemma lem4773605 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4773606 (y : nat) (x : nat) (z : nat) : (term377 x y z) = (term378 y x z).
Proof. exact (@lem4773605 (y = z) (term335 x z)). Qed.
Lemma lem4773616 (x : nat) (y : nat) : (term379 x y) = (term379 x y).
Proof. exact (eq_refl (term379 x y)). Qed.
Lemma lem4773617 (y : nat) (x : nat) (z : nat) : (term373 x y z) = (term380 y x z).
Proof. exact (MK_COMB (@lem4773616 x y) (@lem4773606 y x z)). Qed.
Lemma lem4773621 (q : Prop) (p : Prop) (r : Prop) : (term381 p q r) = (term381 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4773622 (y : nat) (x : nat) (z : nat) : (term380 y x z) = (term382 y x z).
Proof. exact (@lem4773621 (y = z) (term335 x y) (term335 x z)). Qed.
Lemma lem4773644 (y : nat) (x : nat) (z : nat) : (term373 x y z) = (term382 y x z).
Proof. exact (TRANS (@lem4773617 y x z) (@lem4773622 y x z)). Qed.
Lemma lem4773645 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4773646 (y : nat) (x : nat) (z : nat) : (term383 x y z) = (term384 y x z).
Proof. exact (MK_COMB (@lem4773645) (@lem4773644 y x z)). Qed.
Lemma lem4773668 (y : nat) (x : nat) (z : nat) : (term382 y x z) = (term382 y x z).
Proof. exact (eq_refl (term382 y x z)). Qed.
Lemma lem4773669 (y : nat) (x : nat) (z : nat) : ((term373 x y z) = (term382 y x z)) = ((term382 y x z) = (term382 y x z)).
Proof. exact (MK_COMB (@lem4773646 y x z) (@lem4773668 y x z)). Qed.
Lemma lem4773671 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4773672 (x : Prop) : (x = x) = True.
Proof. exact (@lem4773671 Prop x). Qed.
Lemma lem4773673 (y : nat) (x : nat) (z : nat) : ((term382 y x z) = (term382 y x z)) = True.
Proof. exact (@lem4773672 (term382 y x z)). Qed.
Lemma lem4773674 (y : nat) (x : nat) (z : nat) : ((term373 x y z) = (term382 y x z)) = True.
Proof. exact (TRANS (@lem4773669 y x z) (@lem4773673 y x z)). Qed.
Lemma lem4773675 (y : nat) (x : nat) (z : nat) : True = ((term373 x y z) = (term382 y x z)).
Proof. exact (SYM (@lem4773674 y x z)). Qed.
Lemma lem4773676 (y : nat) (x : nat) (z : nat) : (term373 x y z) = (term382 y x z).
Proof. exact (EQ_MP (@lem4773675 y x z) (@lem0)). Qed.
Lemma lem4773677 (y : nat) (x : nat) (z : nat) : term382 y x z.
Proof. exact (EQ_MP (@lem4773676 y x z) (@lem4773570 x y z)). Qed.
Lemma lem4773679 (b : Prop) (a : Prop) : (a \/ b) = (term385 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4773680 (x : nat) (y : nat) (z : nat) : (term382 y x z) = (term386 x y z).
Proof. exact (@lem4773679 (term387 y x z) (y = z)). Qed.
Lemma lem4773682 (a : Prop) (b : Prop) : (term388 a b) = (term389 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4773683 (y : nat) (x : nat) (z : nat) : (term390 y x z) = (term391 y x z).
Proof. exact (@lem4773682 (term335 x y) (term335 x z)). Qed.
Lemma lem4773685 (a : Prop) : (term392 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4773686 (x : nat) (y : nat) : (term393 x y) = (x = y).
Proof. exact (@lem4773685 (x = y)). Qed.
Lemma lem4773687 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4773688 (x : nat) (y : nat) : (term394 x y) = (term395 x y).
Proof. exact (MK_COMB (@lem4773687) (@lem4773686 x y)). Qed.
Lemma lem4773690 (a : Prop) : (term392 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4773691 (x : nat) (z : nat) : (term393 x z) = (x = z).
Proof. exact (@lem4773690 (x = z)). Qed.
Lemma lem4773692 (y : nat) (x : nat) (z : nat) : (term391 y x z) = (term396 y x z).
Proof. exact (MK_COMB (@lem4773688 x y) (@lem4773691 x z)). Qed.
Lemma lem4773693 (y : nat) (x : nat) (z : nat) : (term390 y x z) = (term396 y x z).
Proof. exact (TRANS (@lem4773683 y x z) (@lem4773692 y x z)). Qed.
Lemma lem4773694 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4773695 (y : nat) (x : nat) (z : nat) : (term397 y x z) = (term398 y x z).
Proof. exact (MK_COMB (@lem4773694) (@lem4773693 y x z)). Qed.
Lemma lem4773696 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem4773697 (x : nat) (y : nat) (z : nat) : (term386 x y z) = (term399 x y z).
Proof. exact (MK_COMB (@lem4773695 y x z) (@lem4773696 y z)). Qed.
Lemma lem4773698 (x : nat) (y : nat) (z : nat) : (term382 y x z) = (term399 x y z).
Proof. exact (TRANS (@lem4773680 x y z) (@lem4773697 x y z)). Qed.
Lemma lem4773700 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) : term400 n r x.
Proof. exact (conj (@lem4773579 r n x h1) (@lem4773587 r x)). Qed.
Lemma lem4773702 (x : nat) (y : nat) (z : nat) : term399 x y z.
Proof. exact (EQ_MP (@lem4773698 x y z) (@lem4773677 y x z)). Qed.
Lemma lem4773703 (n : nat) (r : nat -> nat) (x : nat) : term401 n r x.
Proof. exact (@lem4773702 (@I (nat -> nat) r x) (@I (nat -> nat) r n) (@I (nat -> nat) r x)). Qed.
Lemma lem4773706 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) : (@I (nat -> nat) r n) = (@I (nat -> nat) r x).
Proof. exact (@lem4773703 n r x (@lem4773700 r n x h1)). Qed.
Lemma lem4773707 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) : term374 n r x.
Proof. exact (fun h0 : term343 n r x => @lem4773706 r n x h1). Qed.
Lemma lem4773709 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4773710 (n : nat) (r : nat -> nat) (x : nat) : (term374 n r x) = ((@I (nat -> nat) r n) = (@I (nat -> nat) r x)).
Proof. exact (@lem4773709 ((@I (nat -> nat) r n) = (@I (nat -> nat) r x))). Qed.
Lemma lem4773711 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) : (@I (nat -> nat) r n) = (@I (nat -> nat) r x).
Proof. exact (EQ_MP (@lem4773710 n r x) (@lem4773707 r n x h1)). Qed.
Lemma lem4773714 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4773716 (n : nat) (r : nat -> nat) (x : nat) : (term343 n r x) = (term402 n r x).
Proof. exact (@lem4773714 ((@I (nat -> nat) r n) = (@I (nat -> nat) r x))). Qed.
Lemma lem4773719 (n : nat) (r : nat -> nat) (x : nat) (h1 : term343 n r x) : term402 n r x.
Proof. exact (EQ_MP (@lem4773716 n r x) (@lem4772996 n r x h1)). Qed.
Lemma lem4773722 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 n r x) (h2 : term348 r n x) : False.
Proof. exact (@lem4773719 n r x h1 (@lem4773711 r n x h2)). Qed.
Lemma lem4773723 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 n r x) (h2 : term348 r n x) : term372.
Proof. exact (fun h0 : ~ False => @lem4773722 r n x h1 h2). Qed.
Lemma lem4773725 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4773726 : term372 = False.
Proof. exact (@lem4773725 False). Qed.
Lemma lem4773727 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 n r x) (h2 : term348 r n x) : False.
Proof. exact (EQ_MP (@lem4773726) (@lem4773723 r n x h1 h2)). Qed.
Lemma lem4773767 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4773768 (x : nat) : term369 x.
Proof. exact (fun h0 : term355 x => @lem4773767 x). Qed.
Lemma lem4773770 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4773771 (x : nat) : (term369 x) = (x = x).
Proof. exact (@lem4773770 (x = x)). Qed.
Lemma lem4773772 (x : nat) : x = x.
Proof. exact (EQ_MP (@lem4773771 x) (@lem4773768 x)). Qed.
Lemma lem4773775 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4773777 (x : nat) : (term355 x) = (term371 x).
Proof. exact (@lem4773775 (x = x)). Qed.
Lemma lem4773780 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) (h2 : n = x) : term371 x.
Proof. exact (EQ_MP (@lem4773777 x) (@lem4773134 r n x h1 h2)). Qed.
Lemma lem4773783 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) (h2 : n = x) : False.
Proof. exact (@lem4773780 r n x h1 h2 (@lem4773772 x)). Qed.
Lemma lem4773784 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) (h2 : n = x) : term372.
Proof. exact (fun h0 : ~ False => @lem4773783 r n x h1 h2). Qed.
Lemma lem4773786 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4773787 : term372 = False.
Proof. exact (@lem4773786 False). Qed.
Lemma lem4773789 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem4773790 (_58884 : nat) (_58886 : nat) (h1 : _58884 = _58886) : _58884 = _58886.
Proof. exact (h1). Qed.
Lemma lem4773791 (_58885 : nat) (_58887 : nat) (h1 : _58885 = _58887) : _58885 = _58887.
Proof. exact (h1). Qed.
Lemma lem4773792 (_58884 : nat) (_58886 : nat) (h1 : _58884 = _58886) : (Peano.lt _58884) = (Peano.lt _58886).
Proof. exact (MK_COMB (@lem4773789) (@lem4773790 _58884 _58886 h1)). Qed.
Lemma lem4773793 (_58884 : nat) (_58886 : nat) (_58885 : nat) (_58887 : nat) (h1 : _58884 = _58886) (h2 : _58885 = _58887) : (Peano.lt _58884 _58885) = (Peano.lt _58886 _58887).
Proof. exact (MK_COMB (@lem4773792 _58884 _58886 h1) (@lem4773791 _58885 _58887 h2)). Qed.
Lemma lem4773795 (b : Prop) (a : Prop) : term403 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem4773796 (_58886 : nat) (_58887 : nat) (_58884 : nat) (_58885 : nat) : term404 _58886 _58887 _58884 _58885.
Proof. exact (@lem4773795 (Peano.lt _58886 _58887) (Peano.lt _58884 _58885)). Qed.
Lemma lem4773797 (_58884 : nat) (_58886 : nat) (_58885 : nat) (_58887 : nat) (h1 : _58884 = _58886) (h2 : _58885 = _58887) : term405 _58886 _58887 _58884 _58885.
Proof. exact (@lem4773796 _58886 _58887 _58884 _58885 (@lem4773793 _58884 _58886 _58885 _58887 h1 h2)). Qed.
Lemma lem4773798 (_58887 : nat) (_58885 : nat) (_58884 : nat) (_58886 : nat) (h1 : _58884 = _58886) : term406 _58886 _58887 _58884 _58885.
Proof. exact (fun h0 : _58885 = _58887 => @lem4773797 _58884 _58886 _58885 _58887 h1 h0). Qed.
Lemma lem4773800 (a : Prop) (b : Prop) : (a -> b) = (term407 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4773801 (_58886 : nat) (_58887 : nat) (_58884 : nat) (_58885 : nat) : (term406 _58886 _58887 _58884 _58885) = (term408 _58886 _58887 _58884 _58885).
Proof. exact (@lem4773800 (_58885 = _58887) (term405 _58886 _58887 _58884 _58885)). Qed.
Lemma lem4773802 (_58887 : nat) (_58885 : nat) (_58884 : nat) (_58886 : nat) (h1 : _58884 = _58886) : term408 _58886 _58887 _58884 _58885.
Proof. exact (EQ_MP (@lem4773801 _58886 _58887 _58884 _58885) (@lem4773798 _58887 _58885 _58884 _58886 h1)). Qed.
Lemma lem4773803 (_58886 : nat) (_58887 : nat) (_58884 : nat) (_58885 : nat) : term409 _58886 _58887 _58884 _58885.
Proof. exact (fun h0 : _58884 = _58886 => @lem4773802 _58887 _58885 _58884 _58886 h0). Qed.
Lemma lem4773805 (a : Prop) (b : Prop) : (a -> b) = (term407 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4773806 (_58886 : nat) (_58887 : nat) (_58884 : nat) (_58885 : nat) : (term409 _58886 _58887 _58884 _58885) = (term410 _58886 _58887 _58884 _58885).
Proof. exact (@lem4773805 (_58884 = _58886) (term408 _58886 _58887 _58884 _58885)). Qed.
Lemma lem4773807 (_58886 : nat) (_58887 : nat) (_58884 : nat) (_58885 : nat) : term410 _58886 _58887 _58884 _58885.
Proof. exact (EQ_MP (@lem4773806 _58886 _58887 _58884 _58885) (@lem4773803 _58886 _58887 _58884 _58885)). Qed.
Lemma lem4773828 (r : nat -> nat) (x : nat) (n : nat) (h1 : term341 r x n) : (@I (nat -> nat) r x) = (@I (nat -> nat) r n).
Proof. exact (proj1 (@lem4772253 r x n h1)). Qed.
Lemma lem4773829 (r : nat -> nat) (x : nat) (n : nat) (h1 : term341 r x n) : term374 x r n.
Proof. exact (fun h0 : term343 x r n => @lem4773828 r x n h1). Qed.
Lemma lem4773831 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4773832 (x : nat) (r : nat -> nat) (n : nat) : (term374 x r n) = ((@I (nat -> nat) r x) = (@I (nat -> nat) r n)).
Proof. exact (@lem4773831 ((@I (nat -> nat) r x) = (@I (nat -> nat) r n))). Qed.
Lemma lem4773833 (r : nat -> nat) (x : nat) (n : nat) (h1 : term341 r x n) : (@I (nat -> nat) r x) = (@I (nat -> nat) r n).
Proof. exact (EQ_MP (@lem4773832 x r n) (@lem4773829 r x n h1)). Qed.
Lemma lem4773835 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4773836 (r : nat -> nat) (n : nat) : (@I (nat -> nat) r n) = (@I (nat -> nat) r n).
Proof. exact (@lem4773835 (@I (nat -> nat) r n)). Qed.
Lemma lem4773837 (r : nat -> nat) (n : nat) : term375 r n.
Proof. exact (fun h0 : term376 r n => @lem4773836 r n). Qed.
Lemma lem4773839 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4773840 (r : nat -> nat) (n : nat) : (term375 r n) = ((@I (nat -> nat) r n) = (@I (nat -> nat) r n)).
Proof. exact (@lem4773839 ((@I (nat -> nat) r n) = (@I (nat -> nat) r n))). Qed.
Lemma lem4773841 (r : nat -> nat) (n : nat) : (@I (nat -> nat) r n) = (@I (nat -> nat) r n).
Proof. exact (EQ_MP (@lem4773840 r n) (@lem4773837 r n)). Qed.
Lemma lem4773843 (r : nat -> nat) (x : nat) (n : nat) (h1 : term341 r x n) : Peano.lt x n.
Proof. exact (proj1 (@lem4772238 r x n h1)). Qed.
Lemma lem4773844 (r : nat -> nat) (x : nat) (n : nat) (h1 : term341 r x n) : term411 x n.
Proof. exact (fun h0 : term412 x n => @lem4773843 r x n h1). Qed.
Lemma lem4773846 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4773847 (x : nat) (n : nat) : (term411 x n) = (Peano.lt x n).
Proof. exact (@lem4773846 (Peano.lt x n)). Qed.
Lemma lem4773848 (r : nat -> nat) (x : nat) (n : nat) (h1 : term341 r x n) : Peano.lt x n.
Proof. exact (EQ_MP (@lem4773847 x n) (@lem4773844 r x n h1)). Qed.
Lemma lem4773854 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4773855 (r : nat -> nat) (_58757 : nat) (_58758 : nat) : (term330 _58757 r _58758) = (term413 r _58757 _58758).
Proof. exact (@lem4773854 (term328 _58757 r _58758) (term412 _58757 _58758)). Qed.
Lemma lem4773861 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4773862 (r : nat -> nat) (_58757 : nat) (_58758 : nat) : (term414 _58757 r _58758) = (term415 r _58757 _58758).
Proof. exact (MK_COMB (@lem4773861) (@lem4773855 r _58757 _58758)). Qed.
Lemma lem4773868 (r : nat -> nat) (_58757 : nat) (_58758 : nat) : (term413 r _58757 _58758) = (term413 r _58757 _58758).
Proof. exact (eq_refl (term413 r _58757 _58758)). Qed.
Lemma lem4773869 (r : nat -> nat) (_58757 : nat) (_58758 : nat) : ((term330 _58757 r _58758) = (term413 r _58757 _58758)) = ((term413 r _58757 _58758) = (term413 r _58757 _58758)).
Proof. exact (MK_COMB (@lem4773862 r _58757 _58758) (@lem4773868 r _58757 _58758)). Qed.
Lemma lem4773871 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4773872 (x : Prop) : (x = x) = True.
Proof. exact (@lem4773871 Prop x). Qed.
Lemma lem4773873 (r : nat -> nat) (_58757 : nat) (_58758 : nat) : ((term413 r _58757 _58758) = (term413 r _58757 _58758)) = True.
Proof. exact (@lem4773872 (term413 r _58757 _58758)). Qed.
Lemma lem4773874 (r : nat -> nat) (_58757 : nat) (_58758 : nat) : ((term330 _58757 r _58758) = (term413 r _58757 _58758)) = True.
Proof. exact (TRANS (@lem4773869 r _58757 _58758) (@lem4773873 r _58757 _58758)). Qed.
Lemma lem4773875 (r : nat -> nat) (_58757 : nat) (_58758 : nat) : True = ((term330 _58757 r _58758) = (term413 r _58757 _58758)).
Proof. exact (SYM (@lem4773874 r _58757 _58758)). Qed.
Lemma lem4773876 (r : nat -> nat) (_58757 : nat) (_58758 : nat) : (term330 _58757 r _58758) = (term413 r _58757 _58758).
Proof. exact (EQ_MP (@lem4773875 r _58757 _58758) (@lem0)). Qed.
Lemma lem4773877 (_58757 : nat) (_58758 : nat) (r : nat -> nat) (h1 : term21 r) : term413 r _58757 _58758.
Proof. exact (EQ_MP (@lem4773876 r _58757 _58758) (@lem4773162 _58757 _58758 r h1)). Qed.
Lemma lem4773879 (b : Prop) (a : Prop) : (a \/ b) = (term385 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4773880 (_58757 : nat) (r : nat -> nat) (_58758 : nat) : (term413 r _58757 _58758) = (term416 _58757 r _58758).
Proof. exact (@lem4773879 (term412 _58757 _58758) (term328 _58757 r _58758)). Qed.
Lemma lem4773882 (a : Prop) : (term392 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4773883 (_58757 : nat) (_58758 : nat) : (term417 _58757 _58758) = (Peano.lt _58757 _58758).
Proof. exact (@lem4773882 (Peano.lt _58757 _58758)). Qed.
Lemma lem4773884 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4773885 (_58757 : nat) (_58758 : nat) : (term418 _58757 _58758) = (term70 _58757 _58758).
Proof. exact (MK_COMB (@lem4773884) (@lem4773883 _58757 _58758)). Qed.
Lemma lem4773886 (_58757 : nat) (r : nat -> nat) (_58758 : nat) : (term328 _58757 r _58758) = (term328 _58757 r _58758).
Proof. exact (eq_refl (term328 _58757 r _58758)). Qed.
Lemma lem4773887 (_58757 : nat) (r : nat -> nat) (_58758 : nat) : (term416 _58757 r _58758) = (term419 _58757 r _58758).
Proof. exact (MK_COMB (@lem4773885 _58757 _58758) (@lem4773886 _58757 r _58758)). Qed.
Lemma lem4773888 (_58757 : nat) (r : nat -> nat) (_58758 : nat) : (term413 r _58757 _58758) = (term419 _58757 r _58758).
Proof. exact (TRANS (@lem4773880 _58757 r _58758) (@lem4773887 _58757 r _58758)). Qed.
Lemma lem4773891 (_58757 : nat) (_58758 : nat) (r : nat -> nat) (h1 : term21 r) : term419 _58757 r _58758.
Proof. exact (EQ_MP (@lem4773888 _58757 r _58758) (@lem4773877 _58757 _58758 r h1)). Qed.
Lemma lem4773892 (x : nat) (n : nat) (r : nat -> nat) (h1 : term21 r) : term419 x r n.
Proof. exact (@lem4773891 x n r h1). Qed.
Lemma lem4773895 (r : nat -> nat) (x : nat) (n : nat) (h1 : term21 r) (h2 : term341 r x n) : term328 x r n.
Proof. exact (@lem4773892 x n r h1 (@lem4773848 r x n h2)). Qed.
Lemma lem4773896 (r : nat -> nat) (x : nat) (n : nat) (h1 : term21 r) (h2 : term341 r x n) : term420 x r n.
Proof. exact (fun h0 : term421 x r n => @lem4773895 r x n h1 h2). Qed.
Lemma lem4773898 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4773899 (x : nat) (r : nat -> nat) (n : nat) : (term420 x r n) = (term328 x r n).
Proof. exact (@lem4773898 (term328 x r n)). Qed.
Lemma lem4773900 (r : nat -> nat) (x : nat) (n : nat) (h1 : term21 r) (h2 : term341 r x n) : term328 x r n.
Proof. exact (EQ_MP (@lem4773899 x r n) (@lem4773896 r x n h1 h2)). Qed.
Lemma lem4773918 (q : Prop) (p : Prop) (r : Prop) : (term381 p q r) = (term381 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4773919 (_58886 : nat) (_58887 : nat) (_58884 : nat) (_58885 : nat) : (term408 _58886 _58887 _58884 _58885) = (term422 _58886 _58887 _58884 _58885).
Proof. exact (@lem4773918 (Peano.lt _58886 _58887) (term335 _58885 _58887) (term412 _58884 _58885)). Qed.
Lemma lem4773933 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4773934 (_58884 : nat) (_58885 : nat) (_58887 : nat) : (term423 _58887 _58884 _58885) = (term424 _58884 _58885 _58887).
Proof. exact (@lem4773933 (term412 _58884 _58885) (term335 _58885 _58887)). Qed.
Lemma lem4773942 (_58886 : nat) (_58887 : nat) : (term425 _58886 _58887) = (term425 _58886 _58887).
Proof. exact (eq_refl (term425 _58886 _58887)). Qed.
Lemma lem4773943 (_58886 : nat) (_58884 : nat) (_58885 : nat) (_58887 : nat) : (term422 _58886 _58887 _58884 _58885) = (term426 _58886 _58884 _58885 _58887).
Proof. exact (MK_COMB (@lem4773942 _58886 _58887) (@lem4773934 _58884 _58885 _58887)). Qed.
Lemma lem4773954 (_58886 : nat) (_58884 : nat) (_58885 : nat) (_58887 : nat) : (term408 _58886 _58887 _58884 _58885) = (term426 _58886 _58884 _58885 _58887).
Proof. exact (TRANS (@lem4773919 _58886 _58887 _58884 _58885) (@lem4773943 _58886 _58884 _58885 _58887)). Qed.
Lemma lem4773955 (_58884 : nat) (_58886 : nat) : (term379 _58884 _58886) = (term379 _58884 _58886).
Proof. exact (eq_refl (term379 _58884 _58886)). Qed.
Lemma lem4773956 (_58886 : nat) (_58884 : nat) (_58885 : nat) (_58887 : nat) : (term410 _58886 _58887 _58884 _58885) = (term427 _58886 _58884 _58885 _58887).
Proof. exact (MK_COMB (@lem4773955 _58884 _58886) (@lem4773954 _58886 _58884 _58885 _58887)). Qed.
Lemma lem4773960 (q : Prop) (p : Prop) (r : Prop) : (term381 p q r) = (term381 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4773961 (_58886 : nat) (_58884 : nat) (_58885 : nat) (_58887 : nat) : (term427 _58886 _58884 _58885 _58887) = (term428 _58886 _58884 _58885 _58887).
Proof. exact (@lem4773960 (Peano.lt _58886 _58887) (term335 _58884 _58886) (term424 _58884 _58885 _58887)). Qed.
Lemma lem4773975 (q : Prop) (p : Prop) (r : Prop) : (term381 p q r) = (term381 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4773976 (_58884 : nat) (_58886 : nat) (_58885 : nat) (_58887 : nat) : (term429 _58886 _58884 _58885 _58887) = (term430 _58884 _58886 _58885 _58887).
Proof. exact (@lem4773975 (term412 _58884 _58885) (term335 _58884 _58886) (term335 _58885 _58887)). Qed.
Lemma lem4773996 (_58886 : nat) (_58887 : nat) : (term425 _58886 _58887) = (term425 _58886 _58887).
Proof. exact (eq_refl (term425 _58886 _58887)). Qed.
Lemma lem4773997 (_58884 : nat) (_58886 : nat) (_58885 : nat) (_58887 : nat) : (term428 _58886 _58884 _58885 _58887) = (term431 _58884 _58886 _58885 _58887).
Proof. exact (MK_COMB (@lem4773996 _58886 _58887) (@lem4773976 _58884 _58886 _58885 _58887)). Qed.
Lemma lem4774008 (_58884 : nat) (_58886 : nat) (_58885 : nat) (_58887 : nat) : (term427 _58886 _58884 _58885 _58887) = (term431 _58884 _58886 _58885 _58887).
Proof. exact (TRANS (@lem4773961 _58886 _58884 _58885 _58887) (@lem4773997 _58884 _58886 _58885 _58887)). Qed.
Lemma lem4774009 (_58884 : nat) (_58886 : nat) (_58885 : nat) (_58887 : nat) : (term410 _58886 _58887 _58884 _58885) = (term431 _58884 _58886 _58885 _58887).
Proof. exact (TRANS (@lem4773956 _58886 _58884 _58885 _58887) (@lem4774008 _58884 _58886 _58885 _58887)). Qed.
Lemma lem4774010 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4774011 (_58884 : nat) (_58886 : nat) (_58885 : nat) (_58887 : nat) : (term432 _58886 _58887 _58884 _58885) = (term433 _58884 _58886 _58885 _58887).
Proof. exact (MK_COMB (@lem4774010) (@lem4774009 _58884 _58886 _58885 _58887)). Qed.
Lemma lem4774037 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4774038 (_58884 : nat) (_58885 : nat) (_58887 : nat) : (term423 _58887 _58884 _58885) = (term424 _58884 _58885 _58887).
Proof. exact (@lem4774037 (term412 _58884 _58885) (term335 _58885 _58887)). Qed.
Lemma lem4774046 (_58884 : nat) (_58886 : nat) : (term379 _58884 _58886) = (term379 _58884 _58886).
Proof. exact (eq_refl (term379 _58884 _58886)). Qed.
Lemma lem4774047 (_58886 : nat) (_58884 : nat) (_58885 : nat) (_58887 : nat) : (term434 _58886 _58887 _58884 _58885) = (term429 _58886 _58884 _58885 _58887).
Proof. exact (MK_COMB (@lem4774046 _58884 _58886) (@lem4774038 _58884 _58885 _58887)). Qed.
Lemma lem4774051 (q : Prop) (p : Prop) (r : Prop) : (term381 p q r) = (term381 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4774052 (_58884 : nat) (_58886 : nat) (_58885 : nat) (_58887 : nat) : (term429 _58886 _58884 _58885 _58887) = (term430 _58884 _58886 _58885 _58887).
Proof. exact (@lem4774051 (term412 _58884 _58885) (term335 _58884 _58886) (term335 _58885 _58887)). Qed.
Lemma lem4774072 (_58884 : nat) (_58886 : nat) (_58885 : nat) (_58887 : nat) : (term434 _58886 _58887 _58884 _58885) = (term430 _58884 _58886 _58885 _58887).
Proof. exact (TRANS (@lem4774047 _58886 _58884 _58885 _58887) (@lem4774052 _58884 _58886 _58885 _58887)). Qed.
Lemma lem4774073 (_58886 : nat) (_58887 : nat) : (term425 _58886 _58887) = (term425 _58886 _58887).
Proof. exact (eq_refl (term425 _58886 _58887)). Qed.
Lemma lem4774074 (_58884 : nat) (_58886 : nat) (_58885 : nat) (_58887 : nat) : (term435 _58886 _58887 _58884 _58885) = (term431 _58884 _58886 _58885 _58887).
Proof. exact (MK_COMB (@lem4774073 _58886 _58887) (@lem4774072 _58884 _58886 _58885 _58887)). Qed.
Lemma lem4774085 (_58884 : nat) (_58886 : nat) (_58885 : nat) (_58887 : nat) : ((term410 _58886 _58887 _58884 _58885) = (term435 _58886 _58887 _58884 _58885)) = ((term431 _58884 _58886 _58885 _58887) = (term431 _58884 _58886 _58885 _58887)).
Proof. exact (MK_COMB (@lem4774011 _58884 _58886 _58885 _58887) (@lem4774074 _58884 _58886 _58885 _58887)). Qed.
Lemma lem4774087 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4774088 (x : Prop) : (x = x) = True.
Proof. exact (@lem4774087 Prop x). Qed.
Lemma lem4774089 (_58884 : nat) (_58886 : nat) (_58885 : nat) (_58887 : nat) : ((term431 _58884 _58886 _58885 _58887) = (term431 _58884 _58886 _58885 _58887)) = True.
Proof. exact (@lem4774088 (term431 _58884 _58886 _58885 _58887)). Qed.
Lemma lem4774090 (_58886 : nat) (_58887 : nat) (_58884 : nat) (_58885 : nat) : ((term410 _58886 _58887 _58884 _58885) = (term435 _58886 _58887 _58884 _58885)) = True.
Proof. exact (TRANS (@lem4774085 _58884 _58886 _58885 _58887) (@lem4774089 _58884 _58886 _58885 _58887)). Qed.
Lemma lem4774091 (_58886 : nat) (_58887 : nat) (_58884 : nat) (_58885 : nat) : True = ((term410 _58886 _58887 _58884 _58885) = (term435 _58886 _58887 _58884 _58885)).
Proof. exact (SYM (@lem4774090 _58886 _58887 _58884 _58885)). Qed.
Lemma lem4774092 (_58886 : nat) (_58887 : nat) (_58884 : nat) (_58885 : nat) : (term410 _58886 _58887 _58884 _58885) = (term435 _58886 _58887 _58884 _58885).
Proof. exact (EQ_MP (@lem4774091 _58886 _58887 _58884 _58885) (@lem0)). Qed.
Lemma lem4774093 (_58886 : nat) (_58887 : nat) (_58884 : nat) (_58885 : nat) : term435 _58886 _58887 _58884 _58885.
Proof. exact (EQ_MP (@lem4774092 _58886 _58887 _58884 _58885) (@lem4773807 _58886 _58887 _58884 _58885)). Qed.
Lemma lem4774095 (b : Prop) (a : Prop) : (a \/ b) = (term385 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4774096 (_58884 : nat) (_58885 : nat) (_58886 : nat) (_58887 : nat) : (term435 _58886 _58887 _58884 _58885) = (term436 _58884 _58885 _58886 _58887).
Proof. exact (@lem4774095 (term434 _58886 _58887 _58884 _58885) (Peano.lt _58886 _58887)). Qed.
Lemma lem4774098 (a : Prop) (b : Prop) : (term388 a b) = (term389 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4774099 (_58886 : nat) (_58887 : nat) (_58884 : nat) (_58885 : nat) : (term437 _58886 _58887 _58884 _58885) = (term438 _58886 _58887 _58884 _58885).
Proof. exact (@lem4774098 (term335 _58884 _58886) (term423 _58887 _58884 _58885)). Qed.
Lemma lem4774101 (a : Prop) : (term392 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4774102 (_58884 : nat) (_58886 : nat) : (term393 _58884 _58886) = (_58884 = _58886).
Proof. exact (@lem4774101 (_58884 = _58886)). Qed.
Lemma lem4774103 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4774104 (_58884 : nat) (_58886 : nat) : (term394 _58884 _58886) = (term395 _58884 _58886).
Proof. exact (MK_COMB (@lem4774103) (@lem4774102 _58884 _58886)). Qed.
Lemma lem4774106 (a : Prop) (b : Prop) : (term388 a b) = (term389 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4774107 (_58887 : nat) (_58884 : nat) (_58885 : nat) : (term439 _58887 _58884 _58885) = (term440 _58887 _58884 _58885).
Proof. exact (@lem4774106 (term335 _58885 _58887) (term412 _58884 _58885)). Qed.
Lemma lem4774109 (a : Prop) : (term392 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4774110 (_58885 : nat) (_58887 : nat) : (term393 _58885 _58887) = (_58885 = _58887).
Proof. exact (@lem4774109 (_58885 = _58887)). Qed.
Lemma lem4774111 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4774112 (_58885 : nat) (_58887 : nat) : (term394 _58885 _58887) = (term395 _58885 _58887).
Proof. exact (MK_COMB (@lem4774111) (@lem4774110 _58885 _58887)). Qed.
Lemma lem4774114 (a : Prop) : (term392 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4774115 (_58884 : nat) (_58885 : nat) : (term417 _58884 _58885) = (Peano.lt _58884 _58885).
Proof. exact (@lem4774114 (Peano.lt _58884 _58885)). Qed.
Lemma lem4774116 (_58887 : nat) (_58884 : nat) (_58885 : nat) : (term440 _58887 _58884 _58885) = (term441 _58887 _58884 _58885).
Proof. exact (MK_COMB (@lem4774112 _58885 _58887) (@lem4774115 _58884 _58885)). Qed.
Lemma lem4774117 (_58887 : nat) (_58884 : nat) (_58885 : nat) : (term439 _58887 _58884 _58885) = (term441 _58887 _58884 _58885).
Proof. exact (TRANS (@lem4774107 _58887 _58884 _58885) (@lem4774116 _58887 _58884 _58885)). Qed.
Lemma lem4774118 (_58886 : nat) (_58887 : nat) (_58884 : nat) (_58885 : nat) : (term438 _58886 _58887 _58884 _58885) = (term442 _58886 _58887 _58884 _58885).
Proof. exact (MK_COMB (@lem4774104 _58884 _58886) (@lem4774117 _58887 _58884 _58885)). Qed.
Lemma lem4774119 (_58886 : nat) (_58887 : nat) (_58884 : nat) (_58885 : nat) : (term437 _58886 _58887 _58884 _58885) = (term442 _58886 _58887 _58884 _58885).
Proof. exact (TRANS (@lem4774099 _58886 _58887 _58884 _58885) (@lem4774118 _58886 _58887 _58884 _58885)). Qed.
Lemma lem4774120 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4774121 (_58886 : nat) (_58887 : nat) (_58884 : nat) (_58885 : nat) : (term443 _58886 _58887 _58884 _58885) = (term444 _58886 _58887 _58884 _58885).
Proof. exact (MK_COMB (@lem4774120) (@lem4774119 _58886 _58887 _58884 _58885)). Qed.
Lemma lem4774122 (_58886 : nat) (_58887 : nat) : (Peano.lt _58886 _58887) = (Peano.lt _58886 _58887).
Proof. exact (eq_refl (Peano.lt _58886 _58887)). Qed.
Lemma lem4774123 (_58884 : nat) (_58885 : nat) (_58886 : nat) (_58887 : nat) : (term436 _58884 _58885 _58886 _58887) = (term445 _58884 _58885 _58886 _58887).
Proof. exact (MK_COMB (@lem4774121 _58886 _58887 _58884 _58885) (@lem4774122 _58886 _58887)). Qed.
Lemma lem4774124 (_58884 : nat) (_58885 : nat) (_58886 : nat) (_58887 : nat) : (term435 _58886 _58887 _58884 _58885) = (term445 _58884 _58885 _58886 _58887).
Proof. exact (TRANS (@lem4774096 _58884 _58885 _58886 _58887) (@lem4774123 _58884 _58885 _58886 _58887)). Qed.
Lemma lem4774126 (r : nat -> nat) (x : nat) (n : nat) (h1 : term21 r) (h2 : term341 r x n) : term446 x r n.
Proof. exact (conj (@lem4773841 r n) (@lem4773900 r x n h1 h2)). Qed.
Lemma lem4774127 (r : nat -> nat) (x : nat) (n : nat) (h1 : term21 r) (h2 : term341 r x n) : term447 x r n.
Proof. exact (conj (@lem4773833 r x n h2) (@lem4774126 r x n h1 h2)). Qed.
Lemma lem4774129 (_58884 : nat) (_58885 : nat) (_58886 : nat) (_58887 : nat) : term445 _58884 _58885 _58886 _58887.
Proof. exact (EQ_MP (@lem4774124 _58884 _58885 _58886 _58887) (@lem4774093 _58886 _58887 _58884 _58885)). Qed.
Lemma lem4774130 (x : nat) (r : nat -> nat) (n : nat) : term448 x r n.
Proof. exact (@lem4774129 (@I (nat -> nat) r x) (@I (nat -> nat) r n) (@I (nat -> nat) r n) (@I (nat -> nat) r n)). Qed.
Lemma lem4774133 (r : nat -> nat) (x : nat) (n : nat) (h1 : term21 r) (h2 : term341 r x n) : term449 r n.
Proof. exact (@lem4774130 x r n (@lem4774127 r x n h1 h2)). Qed.
Lemma lem4774134 (r : nat -> nat) (x : nat) (n : nat) (h1 : term21 r) (h2 : term341 r x n) : term450 r n.
Proof. exact (fun h0 : term451 r n => @lem4774133 r x n h1 h2). Qed.
Lemma lem4774136 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4774137 (r : nat -> nat) (n : nat) : (term450 r n) = (term449 r n).
Proof. exact (@lem4774136 (term449 r n)). Qed.
Lemma lem4774138 (r : nat -> nat) (x : nat) (n : nat) (h1 : term21 r) (h2 : term341 r x n) : term449 r n.
Proof. exact (EQ_MP (@lem4774137 r n) (@lem4774134 r x n h1 h2)). Qed.
Lemma lem4774141 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4774143 (_58759 : nat) : (term118 _58759) = (term452 _58759).
Proof. exact (@lem4774141 (Peano.lt _58759 _58759)). Qed.
Lemma lem4774146 (_58759 : nat) (h1 : term101) : term452 _58759.
Proof. exact (EQ_MP (@lem4774143 _58759) (@lem4773176 _58759 h1)). Qed.
Lemma lem4774147 (r : nat -> nat) (n : nat) (h1 : term101) : term453 r n.
Proof. exact (@lem4774146 (@I (nat -> nat) r n) h1). Qed.
Lemma lem4774150 (r : nat -> nat) (x : nat) (n : nat) (h1 : term21 r) (h2 : term101) (h3 : term341 r x n) : False.
Proof. exact (@lem4774147 r n h2 (@lem4774138 r x n h1 h3)). Qed.
Lemma lem4774151 (r : nat -> nat) (x : nat) (n : nat) (h1 : term21 r) (h2 : term101) (h3 : term341 r x n) : term372.
Proof. exact (fun h0 : ~ False => @lem4774150 r x n h1 h2 h3). Qed.
Lemma lem4774153 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4774154 : term372 = False.
Proof. exact (@lem4774153 False). Qed.
Lemma lem4774156 (r : nat -> nat) (x : nat) (n : nat) (h1 : term21 r) (h2 : term101) (h3 : term341 r x n) : False.
Proof. exact (EQ_MP (@lem4774154) (@lem4774151 r x n h1 h2 h3)). Qed.
Lemma lem4774158 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) (h2 : n = x) : False.
Proof. exact (EQ_MP (@lem4773787) (@lem4773784 r n x h1 h2)). Qed.
Lemma lem4774159 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 n r x) (h2 : term348 r n x) : (term343 n r x) = False.
Proof. exact (prop_ext (fun h3 : term343 n r x => @lem4773727 r n x h1 h2) (fun h3 : False => @lem4772996 n r x h1)). Qed.
Lemma lem4774161 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 n r x) (h2 : term348 r n x) : False.
Proof. exact (EQ_MP (@lem4774159 r n x h1 h2) (@lem4772996 n r x h1)). Qed.
Lemma lem4774163 (r : nat -> nat) (x : nat) (n : nat) (h1 : term350 r n x) (h2 : x = n) : False.
Proof. exact (EQ_MP (@lem4773533) (@lem4773530 r x n h1 h2)). Qed.
Lemma lem4774164 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 x r n) (h2 : term350 r n x) : (term343 x r n) = False.
Proof. exact (prop_ext (fun h3 : term343 x r n => @lem4773472 r n x h1 h2) (fun h3 : False => @lem4772774 x r n h1)). Qed.
Lemma lem4774166 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 x r n) (h2 : term350 r n x) : False.
Proof. exact (EQ_MP (@lem4774164 r n x h1 h2) (@lem4772774 x r n h1)). Qed.
Lemma lem4774167 (r : nat -> nat) (x : nat) (h1 : term358 r x) : False.
Proof. exact (EQ_MP (@lem4773278) (@lem4773275 r x h1)). Qed.
Lemma lem4774168 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) (h2 : n = x) : (n = x) = False.
Proof. exact (prop_ext (fun h3 : n = x => @lem4774158 r n x h1 h2) (fun h3 : False => @lem4772618 n x h2)). Qed.
Lemma lem4774169 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) (h2 : n = x) : False.
Proof. exact (EQ_MP (@lem4774168 r n x h1 h2) (@lem4772618 n x h2)). Qed.
Lemma lem4774170 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 n r x) (h2 : term348 r n x) : (term343 n r x) = False.
Proof. exact (prop_ext (fun h3 : term343 n r x => @lem4774161 r n x h1 h2) (fun h3 : False => @lem4772602 n r x h1)). Qed.
Lemma lem4774171 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 n r x) (h2 : term348 r n x) : False.
Proof. exact (EQ_MP (@lem4774170 r n x h1 h2) (@lem4772602 n r x h1)). Qed.
Lemma lem4774172 (r : nat -> nat) (x : nat) (n : nat) (h1 : term350 r n x) (h2 : x = n) : (x = n) = False.
Proof. exact (prop_ext (fun h3 : x = n => @lem4774163 r x n h1 h2) (fun h3 : False => @lem4772586 x n h2)). Qed.
Lemma lem4774173 (r : nat -> nat) (x : nat) (n : nat) (h1 : term350 r n x) (h2 : x = n) : False.
Proof. exact (EQ_MP (@lem4774172 r x n h1 h2) (@lem4772586 x n h2)). Qed.
Lemma lem4774174 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 x r n) (h2 : term350 r n x) : (term343 x r n) = False.
Proof. exact (prop_ext (fun h3 : term343 x r n => @lem4774166 r n x h1 h2) (fun h3 : False => @lem4772570 x r n h1)). Qed.
Lemma lem4774175 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 x r n) (h2 : term350 r n x) : False.
Proof. exact (EQ_MP (@lem4774174 r n x h1 h2) (@lem4772570 x r n h1)). Qed.
Lemma lem4774176 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) (h2 : n = x) : (n = x) = False.
Proof. exact (prop_ext (fun h3 : n = x => @lem4774169 r n x h1 h2) (fun h3 : False => @lem4772447 n x h2)). Qed.
Lemma lem4774177 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) (h2 : n = x) : False.
Proof. exact (EQ_MP (@lem4774176 r n x h1 h2) (@lem4772447 n x h2)). Qed.
Lemma lem4774178 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 n r x) (h2 : term348 r n x) : (term343 n r x) = False.
Proof. exact (prop_ext (fun h3 : term343 n r x => @lem4774171 r n x h1 h2) (fun h3 : False => @lem4772408 n r x h1)). Qed.
Lemma lem4774179 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 n r x) (h2 : term348 r n x) : False.
Proof. exact (EQ_MP (@lem4774178 r n x h1 h2) (@lem4772408 n r x h1)). Qed.
Lemma lem4774180 (r : nat -> nat) (x : nat) (n : nat) (h1 : term350 r n x) (h2 : x = n) : (x = n) = False.
Proof. exact (prop_ext (fun h3 : x = n => @lem4774173 r x n h1 h2) (fun h3 : False => @lem4772369 x n h2)). Qed.
Lemma lem4774181 (r : nat -> nat) (x : nat) (n : nat) (h1 : term350 r n x) (h2 : x = n) : False.
Proof. exact (EQ_MP (@lem4774180 r x n h1 h2) (@lem4772369 x n h2)). Qed.
Lemma lem4774182 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 x r n) (h2 : term350 r n x) : (term343 x r n) = False.
Proof. exact (prop_ext (fun h3 : term343 x r n => @lem4774175 r n x h1 h2) (fun h3 : False => @lem4772330 x r n h1)). Qed.
Lemma lem4774183 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 x r n) (h2 : term350 r n x) : False.
Proof. exact (EQ_MP (@lem4774182 r n x h1 h2) (@lem4772330 x r n h1)). Qed.
Lemma lem4774184 (r : nat -> nat) (x : nat) (n : nat) (h1 : term21 r) (h2 : term101) (h3 : term341 r x n) : term101 = False.
Proof. exact (prop_ext (fun h4 : term101 => @lem4774156 r x n h1 h2 h3) (fun h4 : False => @lem4772474 h2)). Qed.
Lemma lem4774185 (r : nat -> nat) (x : nat) (n : nat) (h1 : term21 r) (h2 : term101) (h3 : term341 r x n) : False.
Proof. exact (EQ_MP (@lem4774184 r x n h1 h2 h3) (@lem4772474 h2)). Qed.
Lemma lem4774186 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) (h2 : n = x) : (n = x) = False.
Proof. exact (prop_ext (fun h3 : n = x => @lem4774177 r n x h1 h2) (fun h3 : False => @lem4772447 n x h2)). Qed.
Lemma lem4774187 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) (h2 : n = x) : False.
Proof. exact (EQ_MP (@lem4774186 r n x h1 h2) (@lem4772447 n x h2)). Qed.
Lemma lem4774188 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 n r x) (h2 : term348 r n x) : (term343 n r x) = False.
Proof. exact (prop_ext (fun h3 : term343 n r x => @lem4774179 r n x h1 h2) (fun h3 : False => @lem4772408 n r x h1)). Qed.
Lemma lem4774189 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 n r x) (h2 : term348 r n x) : False.
Proof. exact (EQ_MP (@lem4774188 r n x h1 h2) (@lem4772408 n r x h1)). Qed.
Lemma lem4774190 (r : nat -> nat) (x : nat) (n : nat) (h1 : term350 r n x) (h2 : x = n) : (x = n) = False.
Proof. exact (prop_ext (fun h3 : x = n => @lem4774181 r x n h1 h2) (fun h3 : False => @lem4772369 x n h2)). Qed.
Lemma lem4774191 (r : nat -> nat) (x : nat) (n : nat) (h1 : term350 r n x) (h2 : x = n) : False.
Proof. exact (EQ_MP (@lem4774190 r x n h1 h2) (@lem4772369 x n h2)). Qed.
Lemma lem4774192 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 x r n) (h2 : term350 r n x) : (term343 x r n) = False.
Proof. exact (prop_ext (fun h3 : term343 x r n => @lem4774183 r n x h1 h2) (fun h3 : False => @lem4772330 x r n h1)). Qed.
Lemma lem4774193 (r : nat -> nat) (n : nat) (x : nat) (h1 : term343 x r n) (h2 : term350 r n x) : False.
Proof. exact (EQ_MP (@lem4774192 r n x h1 h2) (@lem4772330 x r n h1)). Qed.
Lemma lem4774194 (r : nat -> nat) (n : nat) (x : nat) (h1 : term348 r n x) : False.
Proof. exact (or_elim (@lem4772247 r n x h1) (fun h0 : term343 n r x => @lem4774189 r n x h0 h1) (fun h0 : n = x => @lem4774187 r n x h1 h0)). Qed.
Lemma lem4774195 (r : nat -> nat) (n : nat) (x : nat) (h1 : term350 r n x) : False.
Proof. exact (or_elim (@lem4772242 r n x h1) (fun h0 : term343 x r n => @lem4774193 r n x h0 h1) (fun h0 : x = n => @lem4774191 r x n h1 h0)). Qed.
Lemma lem4774196 (r : nat -> nat) (n : nat) (x : nat) (h1 : term352 r n x) : False.
Proof. exact (or_elim (@lem4772237 r n x h1) (fun h0 : term350 r n x => @lem4774195 r n x h0) (fun h0 : term348 r n x => @lem4774194 r n x h0)). Qed.
Lemma lem4774197 (r : nat -> nat) (x : nat) (n : nat) (h1 : term21 r) (h2 : term101) (h3 : term354 r x n) : False.
Proof. exact (or_elim (@lem4772234 r x n h3) (fun h0 : term352 r n x => @lem4774196 r n x h0) (fun h0 : term341 r x n => @lem4774185 r x n h1 h2 h0)). Qed.
Lemma lem4774198 (r : nat -> nat) (x : nat) (n : nat) (h1 : term21 r) (h2 : term101) (h3 : term320 r x n) : False.
Proof. exact (or_elim (@lem4772232 r x n h3) (fun h0 : term358 r x => @lem4774167 r x h0) (fun h0 : term354 r x n => @lem4774197 r x n h1 h2 h0)). Qed.
Lemma lem4774199 (r : nat -> nat) (x : nat) (n : nat) (h1 : term21 r) (h2 : term101) (h3 : term320 r x n) : term101 = False.
Proof. exact (prop_ext (fun h4 : term101 => @lem4774198 r x n h1 h2 h3) (fun h4 : False => @lem4772034 h2)). Qed.
Lemma lem4774200 (r : nat -> nat) (x : nat) (n : nat) (h1 : term21 r) (h2 : term101) (h3 : term320 r x n) : False.
Proof. exact (EQ_MP (@lem4774199 r x n h1 h2 h3) (@lem4772034 h2)). Qed.
Lemma lem4774201 (r : nat -> nat) (x : nat) (h1 : term21 r) (h2 : term101) (h3 : term323 r x) : False.
Proof. exact (ex_elim (@lem4771976 r x h3) (fun n : nat => fun h0 : term322 r x n => @lem4774200 r x n h1 h2 h0)). Qed.
Lemma lem4774202 (r : nat -> nat) (h1 : term21 r) (h2 : term101) (h3 : term94 r) : False.
Proof. exact (ex_elim (@lem4771962 r h3) (fun x : nat => fun h0 : term324 r x => @lem4774201 r x h1 h2 h0)). Qed.
Lemma lem4774203 (r : nat -> nat) (h1 : term21 r) (h2 : term101) (h3 : term94 r) : term101 = False.
Proof. exact (prop_ext (fun h4 : term101 => @lem4774202 r h1 h2 h3) (fun h4 : False => @lem4771975 h2)). Qed.
Lemma lem4774204 (r : nat -> nat) (h1 : term21 r) (h2 : term101) (h3 : term94 r) : False.
Proof. exact (EQ_MP (@lem4774203 r h1 h2 h3) (@lem4771975 h2)). Qed.
Lemma lem4774205 (r : nat -> nat) (h1 : term21 r) (h2 : term94 r) : term99.
Proof. exact (fun h0 : term101 => @lem4774204 r h1 h0 h2). Qed.
Lemma lem4774206 : term99 = term100.
Proof. exact (@lem69 term101). Qed.
Lemma lem4774207 (r : nat -> nat) (h1 : term21 r) (h2 : term94 r) : term100.
Proof. exact (EQ_MP (@lem4774206) (@lem4774205 r h1 h2)). Qed.
Lemma lem4774208 (r : nat -> nat) (h1 : term21 r) : term104 r.
Proof. exact (fun h0 : term94 r => @lem4774207 r h1 h0). Qed.
Lemma lem4774209 (s : nat -> Prop) (r : nat -> nat) (h1 : term21 r) : term107 s r.
Proof. exact (fun h0 : s = (@IMAGE nat nat r (@UNIV nat)) => @lem4774208 r h1). Qed.
Lemma lem4774210 (s : nat -> Prop) (r : nat -> nat) : term109 s r.
Proof. exact (fun h0 : term21 r => @lem4774209 s r h0). Qed.
Lemma lem4774215 (r : nat -> nat) : term113 r.
Proof. exact (fun s : nat -> Prop => @lem4774210 s r). Qed.
Lemma lem4774220 : term117.
Proof. exact (fun r : nat -> nat => @lem4774215 r). Qed.
Lemma lem4774221 : term116.
Proof. exact (EQ_MP (@lem4771217) (@lem4774220)). Qed.
Lemma lem4774222 (r : nat -> nat) : term454 r.
Proof. exact (@lem4774221 r). Qed.
Lemma lem4774223 (r : nat -> nat) : (term454 r) = (term112 r).
Proof. exact (eq_refl (term454 r)). Qed.
Lemma lem4774224 (r : nat -> nat) : term112 r.
Proof. exact (EQ_MP (@lem4774223 r) (@lem4774222 r)). Qed.
Lemma lem4774225 (r : nat -> nat) (s : nat -> Prop) : term455 r s.
Proof. exact (@lem4774224 r s). Qed.
Lemma lem4774226 (s : nat -> Prop) (r : nat -> nat) : (term455 r s) = (term95 s r).
Proof. exact (eq_refl (term455 r s)). Qed.
Lemma lem4774227 (s : nat -> Prop) (r : nat -> nat) : term95 s r.
Proof. exact (EQ_MP (@lem4774226 s r) (@lem4774225 r s)). Qed.
Lemma lem4774229 (s : nat -> Prop) (r : nat -> nat) : term95 s r.
Proof. exact (@lem4770951 s r (@lem4774227 s r)). Qed.
Lemma lem4774230 (s : nat -> Prop) (r : nat -> nat) (h1 : term21 r) : term106 s r.
Proof. exact (@lem4774229 s r (@lem4770756 r h1)). Qed.
Lemma lem4774231 (s : nat -> Prop) (r : nat -> nat) (h1 : term21 r) (h2 : s = (@IMAGE nat nat r (@UNIV nat))) : term103 r.
Proof. exact (@lem4774230 s r h1 (@lem4770755 s r h2)). Qed.
Lemma lem4774232 (s : nat -> Prop) (r : nat -> nat) (h1 : term21 r) (h2 : term94 r) (h3 : s = (@IMAGE nat nat r (@UNIV nat))) : term99.
Proof. exact (@lem4774231 s r h1 h3 (@lem4770936 r h2)). Qed.
Lemma lem4774233 (s : nat -> Prop) (r : nat -> nat) (h1 : term21 r) (h2 : term94 r) (h3 : s = (@IMAGE nat nat r (@UNIV nat))) : False.
Proof. exact (@lem4774232 s r h1 h2 h3 (@lem91686)). Qed.
Lemma lem4774234 (s : nat -> Prop) (r : nat -> nat) (h1 : term21 r) (h2 : term94 r) (h3 : s = (@IMAGE nat nat r (@UNIV nat))) : (term94 r) = False.
Proof. exact (prop_ext (fun h4 : term94 r => @lem4774233 s r h1 h2 h3) (fun h4 : False => @lem4770936 r h2)). Qed.
Lemma lem4774235 (s : nat -> Prop) (r : nat -> nat) (h1 : term21 r) (h2 : term94 r) (h3 : s = (@IMAGE nat nat r (@UNIV nat))) : False.
Proof. exact (EQ_MP (@lem4774234 s r h1 h2 h3) (@lem4770936 r h2)). Qed.
Lemma lem4774236 (s : nat -> Prop) (r : nat -> nat) (h1 : term21 r) (h2 : s = (@IMAGE nat nat r (@UNIV nat))) : term93 r.
Proof. exact (fun h0 : term94 r => @lem4774235 s r h1 h0 h2). Qed.
Lemma lem4774237 (s : nat -> Prop) (r : nat -> nat) (h1 : term21 r) (h2 : s = (@IMAGE nat nat r (@UNIV nat))) : term84 r.
Proof. exact (EQ_MP (@lem4770935 r) (@lem4774236 s r h1 h2)). Qed.
Lemma lem4774238 (s : nat -> Prop) (r : nat -> nat) (h1 : term21 r) (h2 : s = (@IMAGE nat nat r (@UNIV nat))) : term41 r.
Proof. exact (@lem4770931 r (@lem4774237 s r h1 h2)). Qed.
Lemma lem4774239 (s : nat -> Prop) (r : nat -> nat) (h1 : term21 r) (h2 : s = (@IMAGE nat nat r (@UNIV nat))) : term42 r.
Proof. exact (EQ_MP (@lem4770867 r) (@lem4774238 s r h1 h2)). Qed.
Lemma lem4774240 (s : nat -> Prop) (r : nat -> nat) (h1 : term21 r) (h2 : s = (@IMAGE nat nat r (@UNIV nat))) : term22 r.
Proof. exact (@lem4770773 r (@lem4774239 s r h1 h2)). Qed.
Lemma lem4774241 (s : nat -> Prop) (r : nat -> nat) (h1 : term21 r) (h2 : s = (@IMAGE nat nat r (@UNIV nat))) : @INFINITE nat s.
Proof. exact (EQ_MP (@lem4770769 s r h2) (@lem4774240 s r h1 h2)). Qed.
Lemma lem4774242 (r : nat -> nat) (s : nat -> Prop) (h1 : term18 r s) : s = (@IMAGE nat nat r (@UNIV nat)).
Proof. exact (proj2 (@lem4770754 r s h1)). Qed.
Lemma lem4774243 (r : nat -> nat) (s : nat -> Prop) (h1 : term18 r s) : term21 r.
Proof. exact (proj1 (@lem4770754 r s h1)). Qed.
Lemma lem4774244 (s : nat -> Prop) (r : nat -> nat) (h1 : term21 r) (h2 : s = (@IMAGE nat nat r (@UNIV nat))) : (s = (@IMAGE nat nat r (@UNIV nat))) = (@INFINITE nat s).
Proof. exact (prop_ext (fun h3 : s = (@IMAGE nat nat r (@UNIV nat)) => @lem4774241 s r h1 h2) (fun h3 : @INFINITE nat s => @lem4770755 s r h2)). Qed.
Lemma lem4774245 (s : nat -> Prop) (r : nat -> nat) (h1 : term21 r) (h2 : s = (@IMAGE nat nat r (@UNIV nat))) : @INFINITE nat s.
Proof. exact (EQ_MP (@lem4774244 s r h1 h2) (@lem4770755 s r h2)). Qed.
Lemma lem4774246 (s : nat -> Prop) (r : nat -> nat) (h1 : term21 r) (h2 : s = (@IMAGE nat nat r (@UNIV nat))) : (term21 r) = (@INFINITE nat s).
Proof. exact (prop_ext (fun h3 : term21 r => @lem4774245 s r h1 h2) (fun h3 : @INFINITE nat s => @lem4770756 r h1)). Qed.
Lemma lem4774247 (s : nat -> Prop) (r : nat -> nat) (h1 : term21 r) (h2 : s = (@IMAGE nat nat r (@UNIV nat))) : @INFINITE nat s.
Proof. exact (EQ_MP (@lem4774246 s r h1 h2) (@lem4770756 r h1)). Qed.
Lemma lem4774248 (r : nat -> nat) (s : nat -> Prop) (h1 : term21 r) (h2 : term18 r s) : (s = (@IMAGE nat nat r (@UNIV nat))) = (@INFINITE nat s).
Proof. exact (prop_ext (fun h3 : s = (@IMAGE nat nat r (@UNIV nat)) => @lem4774247 s r h1 h3) (fun h3 : @INFINITE nat s => @lem4774242 r s h2)). Qed.
Lemma lem4774249 (r : nat -> nat) (s : nat -> Prop) (h1 : term21 r) (h2 : term18 r s) : @INFINITE nat s.
Proof. exact (EQ_MP (@lem4774248 r s h1 h2) (@lem4774242 r s h2)). Qed.
Lemma lem4774250 (r : nat -> nat) (s : nat -> Prop) (h1 : term18 r s) : (term21 r) = (@INFINITE nat s).
Proof. exact (prop_ext (fun h2 : term21 r => @lem4774249 r s h2 h1) (fun h2 : @INFINITE nat s => @lem4774243 r s h1)). Qed.
Lemma lem4774251 (r : nat -> nat) (s : nat -> Prop) (h1 : term18 r s) : @INFINITE nat s.
Proof. exact (EQ_MP (@lem4774250 r s h1) (@lem4774243 r s h1)). Qed.
Lemma lem4774252 (s : nat -> Prop) (h1 : term17 s) : @INFINITE nat s.
Proof. exact (ex_elim (@lem4770739 s h1) (fun r : nat -> nat => fun h0 : term456 s r => @lem4774251 r s h0)). Qed.
Lemma lem4774254 (s : nat -> Prop) : term457 s.
Proof. exact (fun h0 : term17 s => @lem4774252 s h0). Qed.
Lemma lem4774255 (s : nat -> Prop) : term458 s.
Proof. exact (conj (@lem4770716 s) (@lem4774254 s)). Qed.
Lemma lem4774256 (s : nat -> Prop) : (term458 s) = ((@INFINITE nat s) = (term17 s)).
Proof. exact (@lem32 (@INFINITE nat s) (term17 s)). Qed.
Lemma lem4774257 (s : nat -> Prop) : (@INFINITE nat s) = (term17 s).
Proof. exact (EQ_MP (@lem4774256 s) (@lem4774255 s)). Qed.
Lemma lem4774262 : term459.
Proof. exact (fun s : nat -> Prop => @lem4774257 s). Qed.
