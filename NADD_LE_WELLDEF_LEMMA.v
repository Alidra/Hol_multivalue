Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_LE_WELLDEF_LEMMA_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import FORALL_AND_THM_spec.
Require Import LE_ADD_RCANCEL_spec.
Require Import nadd_eq_spec.
Require Import nadd_le_spec.
Require Import thm0_spec.
Require Import thm1247096_spec.
Require Import thm272809_spec.
Require Import thm7_spec.
Lemma lem1269693 (m : nat) : term0 m.
Proof. exact (@lem100973 m). Qed.
Lemma lem1269694 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1269695 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1269694 m) (@lem1269693 m)). Qed.
Lemma lem1269696 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1269695 m n). Qed.
Lemma lem1269697 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1269698 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem1269697 m n) (@lem1269696 m n)). Qed.
Lemma lem1269699 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem1269698 m n p). Qed.
Lemma lem1269700 (p : nat) (m : nat) (n : nat) : (term4 m n p) = ((term5 m n p) = (Peano.le m n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem1269702 (m : nat) : term6 m.
Proof. exact (@lem77960 m). Qed.
Lemma lem1269703 (m : nat) : (term6 m) = (term7 m).
Proof. exact (eq_refl (term6 m)). Qed.
Lemma lem1269704 (m : nat) : term7 m.
Proof. exact (EQ_MP (@lem1269703 m) (@lem1269702 m)). Qed.
Lemma lem1269705 (m : nat) (n : nat) : term8 m n.
Proof. exact (@lem1269704 m n). Qed.
Lemma lem1269706 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem1269707 (m : nat) (n : nat) : term9 m n.
Proof. exact (EQ_MP (@lem1269706 m n) (@lem1269705 m n)). Qed.
Lemma lem1269708 (m : nat) (n : nat) (p : nat) : term10 m n p.
Proof. exact (@lem1269707 m n p). Qed.
Lemma lem1269709 (m : nat) (n : nat) (p : nat) : (term10 m n p) = ((term11 m n p) = (term12 m n p)).
Proof. exact (eq_refl (term10 m n p)). Qed.
Lemma lem1269711 {A : Type'} (P : A -> Prop) : term13 A P.
Proof. exact (@lem4997 A P). Qed.
Lemma lem1269712 {A : Type'} (P : A -> Prop) : (term13 A P) = (term14 A P).
Proof. exact (eq_refl (term13 A P)). Qed.
Lemma lem1269713 {A : Type'} (P : A -> Prop) : term14 A P.
Proof. exact (EQ_MP (@lem1269712 A P) (@lem1269711 A P)). Qed.
Lemma lem1269714 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term15 A P Q.
Proof. exact (@lem1269713 A P Q). Qed.
Lemma lem1269715 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term15 A P Q) = ((term16 A P Q) = (term17 A P Q)).
Proof. exact (eq_refl (term15 A P Q)). Qed.
Lemma lem1269717 (m : nat) : term18 m.
Proof. exact (@lem1247096 m). Qed.
Lemma lem1269718 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem1269719 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem1269718 m) (@lem1269717 m)). Qed.
Lemma lem1269720 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem1269719 m n). Qed.
Lemma lem1269721 (n : nat) (m : nat) : (term20 m n) = (term21 n m).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem1269722 (n : nat) (m : nat) : term21 n m.
Proof. exact (EQ_MP (@lem1269721 n m) (@lem1269720 m n)). Qed.
Lemma lem1269723 (n : nat) (m : nat) (p : nat) : term22 n m p.
Proof. exact (@lem1269722 n m p). Qed.
Lemma lem1269724 (n : nat) (m : nat) (p : nat) : (term22 n m p) = ((term23 m n p) = (term24 n m p)).
Proof. exact (eq_refl (term22 n m p)). Qed.
Lemma lem1269726 (x : nadd) : term25 x.
Proof. exact (@lem1269692 x). Qed.
Lemma lem1269727 (x : nadd) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1269728 (x : nadd) : term26 x.
Proof. exact (EQ_MP (@lem1269727 x) (@lem1269726 x)). Qed.
Lemma lem1269729 (x : nadd) (y : nadd) : term27 x y.
Proof. exact (@lem1269728 x y). Qed.
Lemma lem1269730 (x : nadd) (y : nadd) : (term27 x y) = ((nadd_le x y) = (term28 x y)).
Proof. exact (eq_refl (term27 x y)). Qed.
Lemma lem1269732 (x : nadd) : term29 x.
Proof. exact (@lem1267930 x). Qed.
Lemma lem1269733 (x : nadd) : (term29 x) = (term30 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1269734 (x : nadd) : term30 x.
Proof. exact (EQ_MP (@lem1269733 x) (@lem1269732 x)). Qed.
Lemma lem1269735 (x : nadd) (y : nadd) : term31 x y.
Proof. exact (@lem1269734 x y). Qed.
Lemma lem1269736 (x : nadd) (y : nadd) : (term31 x y) = ((nadd_eq x y) = (term32 x y)).
Proof. exact (eq_refl (term31 x y)). Qed.
Lemma lem1269743 (x : nadd) (y : nadd) : (nadd_eq x y) = (term32 x y).
Proof. exact (EQ_MP (@lem1269736 x y) (@lem1269735 x y)). Qed.
Lemma lem1269744 (x : nadd) (x' : nadd) : (nadd_eq x x') = (term32 x x').
Proof. exact (@lem1269743 x x'). Qed.
Lemma lem1269753 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1269754 (x : nadd) (x' : nadd) : (term33 x x') = (term34 x x').
Proof. exact (MK_COMB (@lem1269753) (@lem1269744 x x')). Qed.
Lemma lem1269758 (x : nadd) (y : nadd) : (nadd_eq x y) = (term32 x y).
Proof. exact (EQ_MP (@lem1269736 x y) (@lem1269735 x y)). Qed.
Lemma lem1269759 (y : nadd) (y' : nadd) : (nadd_eq y y') = (term32 y y').
Proof. exact (@lem1269758 y y'). Qed.
Lemma lem1269768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1269769 (y : nadd) (y' : nadd) : (term33 y y') = (term34 y y').
Proof. exact (MK_COMB (@lem1269768) (@lem1269759 y y')). Qed.
Lemma lem1269771 (x : nadd) (y : nadd) : (nadd_le x y) = (term28 x y).
Proof. exact (EQ_MP (@lem1269730 x y) (@lem1269729 x y)). Qed.
Lemma lem1269780 (y' : nadd) (x : nadd) (y : nadd) : (term35 y' x y) = (term36 y' x y).
Proof. exact (MK_COMB (@lem1269769 y y') (@lem1269771 x y)). Qed.
Lemma lem1269783 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) : (term37 x' y' x y) = (term38 x' y' x y).
Proof. exact (MK_COMB (@lem1269754 x x') (@lem1269780 y' x y)). Qed.
Lemma lem1269786 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1269787 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) : (term39 x' y' x y) = (term40 x' y' x y).
Proof. exact (MK_COMB (@lem1269786) (@lem1269783 x' y' x y)). Qed.
Lemma lem1269789 (x : nadd) (y : nadd) : (nadd_le x y) = (term28 x y).
Proof. exact (EQ_MP (@lem1269730 x y) (@lem1269729 x y)). Qed.
Lemma lem1269790 (x' : nadd) (y' : nadd) : (nadd_le x' y') = (term28 x' y').
Proof. exact (@lem1269789 x' y'). Qed.
Lemma lem1269799 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term41 x y x' y') = (term42 x y x' y').
Proof. exact (MK_COMB (@lem1269787 x' y' x y) (@lem1269790 x' y')). Qed.
Lemma lem1269802 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term42 x y x' y') = (term41 x y x' y').
Proof. exact (SYM (@lem1269799 x y x' y')). Qed.
Lemma lem1269816 (n : nat) (m : nat) (p : nat) : (term23 m n p) = (term24 n m p).
Proof. exact (EQ_MP (@lem1269724 n m p) (@lem1269723 n m p)). Qed.
Lemma lem1269817 (x' : nadd) (x : nadd) (n : nat) (B : nat) : (term43 x x' n B) = (term44 x' x n B).
Proof. exact (@lem1269816 (dest_nadd x' n) (dest_nadd x n) B). Qed.
Lemma lem1269820 (x' : nadd) (x : nadd) (B : nat) : (term45 x x' B) = (term46 x' x B).
Proof. exact (fun_ext (fun n : nat => @lem1269817 x' x n B)). Qed.
Lemma lem1269821 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1269822 (x' : nadd) (x : nadd) (B : nat) : (term47 x x' B) = (term48 x' x B).
Proof. exact (MK_COMB (@lem1269821) (@lem1269820 x' x B)). Qed.
Lemma lem1269824 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term16 A P Q) = (term17 A P Q).
Proof. exact (EQ_MP (@lem1269715 A P Q) (@lem1269714 A P Q)). Qed.
Lemma lem1269825 (P : nat -> Prop) (Q : nat -> Prop) : (term49 P Q) = (term50 P Q).
Proof. exact (@lem1269824 nat P Q). Qed.
Lemma lem1269826 (x' : nadd) (x : nadd) (B : nat) : (term51 x' x B) = (term52 x' x B).
Proof. exact (@lem1269825 (term53 x x' B) (term53 x' x B)). Qed.
Lemma lem1269827 (x : nadd) (x' : nadd) (n : nat) (B : nat) : (term54 x x' B n) = (term55 x x' n B).
Proof. exact (eq_refl (term54 x x' B n)). Qed.
Lemma lem1269828 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1269829 (x : nadd) (x' : nadd) (n : nat) (B : nat) : (term56 x x' B n) = (term57 x x' n B).
Proof. exact (MK_COMB (@lem1269828) (@lem1269827 x x' n B)). Qed.
Lemma lem1269830 (x' : nadd) (x : nadd) (n : nat) (B : nat) : (term54 x' x B n) = (term55 x' x n B).
Proof. exact (eq_refl (term54 x' x B n)). Qed.
Lemma lem1269831 (x' : nadd) (x : nadd) (n : nat) (B : nat) : (term58 x' x B n) = (term44 x' x n B).
Proof. exact (MK_COMB (@lem1269829 x x' n B) (@lem1269830 x' x n B)). Qed.
Lemma lem1269832 (x' : nadd) (x : nadd) (B : nat) : (term59 x' x B) = (term46 x' x B).
Proof. exact (fun_ext (fun n : nat => @lem1269831 x' x n B)). Qed.
Lemma lem1269833 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1269834 (x' : nadd) (x : nadd) (B : nat) : (term51 x' x B) = (term48 x' x B).
Proof. exact (MK_COMB (@lem1269833) (@lem1269832 x' x B)). Qed.
Lemma lem1269835 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1269836 (x' : nadd) (x : nadd) (B : nat) : (term60 x' x B) = (term61 x' x B).
Proof. exact (MK_COMB (@lem1269835) (@lem1269834 x' x B)). Qed.
Lemma lem1269837 (x : nadd) (x' : nadd) (n : nat) (B : nat) : (term54 x x' B n) = (term55 x x' n B).
Proof. exact (eq_refl (term54 x x' B n)). Qed.
Lemma lem1269838 (x : nadd) (x' : nadd) (B : nat) : (term62 x x' B) = (term53 x x' B).
Proof. exact (fun_ext (fun n : nat => @lem1269837 x x' n B)). Qed.
Lemma lem1269839 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1269840 (x : nadd) (x' : nadd) (B : nat) : (term63 x x' B) = (term64 x x' B).
Proof. exact (MK_COMB (@lem1269839) (@lem1269838 x x' B)). Qed.
Lemma lem1269841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1269842 (x : nadd) (x' : nadd) (B : nat) : (term65 x x' B) = (term66 x x' B).
Proof. exact (MK_COMB (@lem1269841) (@lem1269840 x x' B)). Qed.
Lemma lem1269843 (x' : nadd) (x : nadd) (n : nat) (B : nat) : (term54 x' x B n) = (term55 x' x n B).
Proof. exact (eq_refl (term54 x' x B n)). Qed.
Lemma lem1269844 (x' : nadd) (x : nadd) (B : nat) : (term62 x' x B) = (term53 x' x B).
Proof. exact (fun_ext (fun n : nat => @lem1269843 x' x n B)). Qed.
Lemma lem1269845 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1269846 (x' : nadd) (x : nadd) (B : nat) : (term63 x' x B) = (term64 x' x B).
Proof. exact (MK_COMB (@lem1269845) (@lem1269844 x' x B)). Qed.
Lemma lem1269847 (x' : nadd) (x : nadd) (B : nat) : (term52 x' x B) = (term67 x' x B).
Proof. exact (MK_COMB (@lem1269842 x x' B) (@lem1269846 x' x B)). Qed.
Lemma lem1269848 (x' : nadd) (x : nadd) (B : nat) : ((term51 x' x B) = (term52 x' x B)) = ((term48 x' x B) = (term67 x' x B)).
Proof. exact (MK_COMB (@lem1269836 x' x B) (@lem1269847 x' x B)). Qed.
Lemma lem1269849 (x' : nadd) (x : nadd) (B : nat) : (term48 x' x B) = (term67 x' x B).
Proof. exact (EQ_MP (@lem1269848 x' x B) (@lem1269826 x' x B)). Qed.
Lemma lem1269860 (x' : nadd) (x : nadd) (B : nat) : (term47 x x' B) = (term67 x' x B).
Proof. exact (TRANS (@lem1269822 x' x B) (@lem1269849 x' x B)). Qed.
Lemma lem1269861 (x' : nadd) (x : nadd) : (term68 x x') = (term69 x' x).
Proof. exact (fun_ext (fun B : nat => @lem1269860 x' x B)). Qed.
Lemma lem1269862 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1269863 (x' : nadd) (x : nadd) : (term32 x x') = (term70 x' x).
Proof. exact (MK_COMB (@lem1269862) (@lem1269861 x' x)). Qed.
Lemma lem1269868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1269869 (x' : nadd) (x : nadd) : (term34 x x') = (term71 x' x).
Proof. exact (MK_COMB (@lem1269868) (@lem1269863 x' x)). Qed.
Lemma lem1269881 (n : nat) (m : nat) (p : nat) : (term23 m n p) = (term24 n m p).
Proof. exact (EQ_MP (@lem1269724 n m p) (@lem1269723 n m p)). Qed.
Lemma lem1269882 (y' : nadd) (y : nadd) (n : nat) (B : nat) : (term43 y y' n B) = (term44 y' y n B).
Proof. exact (@lem1269881 (dest_nadd y' n) (dest_nadd y n) B). Qed.
Lemma lem1269885 (y' : nadd) (y : nadd) (B : nat) : (term45 y y' B) = (term46 y' y B).
Proof. exact (fun_ext (fun n : nat => @lem1269882 y' y n B)). Qed.
Lemma lem1269886 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1269887 (y' : nadd) (y : nadd) (B : nat) : (term47 y y' B) = (term48 y' y B).
Proof. exact (MK_COMB (@lem1269886) (@lem1269885 y' y B)). Qed.
Lemma lem1269889 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term16 A P Q) = (term17 A P Q).
Proof. exact (EQ_MP (@lem1269715 A P Q) (@lem1269714 A P Q)). Qed.
Lemma lem1269890 (P : nat -> Prop) (Q : nat -> Prop) : (term49 P Q) = (term50 P Q).
Proof. exact (@lem1269889 nat P Q). Qed.
Lemma lem1269891 (y' : nadd) (y : nadd) (B : nat) : (term51 y' y B) = (term52 y' y B).
Proof. exact (@lem1269890 (term53 y y' B) (term53 y' y B)). Qed.
Lemma lem1269892 (y : nadd) (y' : nadd) (n : nat) (B : nat) : (term54 y y' B n) = (term55 y y' n B).
Proof. exact (eq_refl (term54 y y' B n)). Qed.
Lemma lem1269893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1269894 (y : nadd) (y' : nadd) (n : nat) (B : nat) : (term56 y y' B n) = (term57 y y' n B).
Proof. exact (MK_COMB (@lem1269893) (@lem1269892 y y' n B)). Qed.
Lemma lem1269895 (y' : nadd) (y : nadd) (n : nat) (B : nat) : (term54 y' y B n) = (term55 y' y n B).
Proof. exact (eq_refl (term54 y' y B n)). Qed.
Lemma lem1269896 (y' : nadd) (y : nadd) (n : nat) (B : nat) : (term58 y' y B n) = (term44 y' y n B).
Proof. exact (MK_COMB (@lem1269894 y y' n B) (@lem1269895 y' y n B)). Qed.
Lemma lem1269897 (y' : nadd) (y : nadd) (B : nat) : (term59 y' y B) = (term46 y' y B).
Proof. exact (fun_ext (fun n : nat => @lem1269896 y' y n B)). Qed.
Lemma lem1269898 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1269899 (y' : nadd) (y : nadd) (B : nat) : (term51 y' y B) = (term48 y' y B).
Proof. exact (MK_COMB (@lem1269898) (@lem1269897 y' y B)). Qed.
Lemma lem1269900 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1269901 (y' : nadd) (y : nadd) (B : nat) : (term60 y' y B) = (term61 y' y B).
Proof. exact (MK_COMB (@lem1269900) (@lem1269899 y' y B)). Qed.
Lemma lem1269902 (y : nadd) (y' : nadd) (n : nat) (B : nat) : (term54 y y' B n) = (term55 y y' n B).
Proof. exact (eq_refl (term54 y y' B n)). Qed.
Lemma lem1269903 (y : nadd) (y' : nadd) (B : nat) : (term62 y y' B) = (term53 y y' B).
Proof. exact (fun_ext (fun n : nat => @lem1269902 y y' n B)). Qed.
Lemma lem1269904 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1269905 (y : nadd) (y' : nadd) (B : nat) : (term63 y y' B) = (term64 y y' B).
Proof. exact (MK_COMB (@lem1269904) (@lem1269903 y y' B)). Qed.
Lemma lem1269906 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1269907 (y : nadd) (y' : nadd) (B : nat) : (term65 y y' B) = (term66 y y' B).
Proof. exact (MK_COMB (@lem1269906) (@lem1269905 y y' B)). Qed.
Lemma lem1269908 (y' : nadd) (y : nadd) (n : nat) (B : nat) : (term54 y' y B n) = (term55 y' y n B).
Proof. exact (eq_refl (term54 y' y B n)). Qed.
Lemma lem1269909 (y' : nadd) (y : nadd) (B : nat) : (term62 y' y B) = (term53 y' y B).
Proof. exact (fun_ext (fun n : nat => @lem1269908 y' y n B)). Qed.
Lemma lem1269910 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1269911 (y' : nadd) (y : nadd) (B : nat) : (term63 y' y B) = (term64 y' y B).
Proof. exact (MK_COMB (@lem1269910) (@lem1269909 y' y B)). Qed.
Lemma lem1269912 (y' : nadd) (y : nadd) (B : nat) : (term52 y' y B) = (term67 y' y B).
Proof. exact (MK_COMB (@lem1269907 y y' B) (@lem1269911 y' y B)). Qed.
Lemma lem1269913 (y' : nadd) (y : nadd) (B : nat) : ((term51 y' y B) = (term52 y' y B)) = ((term48 y' y B) = (term67 y' y B)).
Proof. exact (MK_COMB (@lem1269901 y' y B) (@lem1269912 y' y B)). Qed.
Lemma lem1269914 (y' : nadd) (y : nadd) (B : nat) : (term48 y' y B) = (term67 y' y B).
Proof. exact (EQ_MP (@lem1269913 y' y B) (@lem1269891 y' y B)). Qed.
Lemma lem1269925 (y' : nadd) (y : nadd) (B : nat) : (term47 y y' B) = (term67 y' y B).
Proof. exact (TRANS (@lem1269887 y' y B) (@lem1269914 y' y B)). Qed.
Lemma lem1269926 (y' : nadd) (y : nadd) : (term68 y y') = (term69 y' y).
Proof. exact (fun_ext (fun B : nat => @lem1269925 y' y B)). Qed.
Lemma lem1269927 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1269928 (y' : nadd) (y : nadd) : (term32 y y') = (term70 y' y).
Proof. exact (MK_COMB (@lem1269927) (@lem1269926 y' y)). Qed.
Lemma lem1269933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1269934 (y' : nadd) (y : nadd) : (term34 y y') = (term71 y' y).
Proof. exact (MK_COMB (@lem1269933) (@lem1269928 y' y)). Qed.
Lemma lem1269943 (x : nadd) (y : nadd) : (term28 x y) = (term28 x y).
Proof. exact (eq_refl (term28 x y)). Qed.
Lemma lem1269944 (y' : nadd) (x : nadd) (y : nadd) : (term36 y' x y) = (term72 y' x y).
Proof. exact (MK_COMB (@lem1269934 y' y) (@lem1269943 x y)). Qed.
Lemma lem1269947 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) : (term38 x' y' x y) = (term73 x' y' x y).
Proof. exact (MK_COMB (@lem1269869 x' x) (@lem1269944 y' x y)). Qed.
Lemma lem1269950 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1269951 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) : (term40 x' y' x y) = (term74 x' y' x y).
Proof. exact (MK_COMB (@lem1269950) (@lem1269947 x' y' x y)). Qed.
Lemma lem1269960 (x' : nadd) (y' : nadd) : (term28 x' y') = (term28 x' y').
Proof. exact (eq_refl (term28 x' y')). Qed.
Lemma lem1269961 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term42 x y x' y') = (term75 x y x' y').
Proof. exact (MK_COMB (@lem1269951 x' y' x y) (@lem1269960 x' y')). Qed.
Lemma lem1269964 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term75 x y x' y') = (term42 x y x' y').
Proof. exact (SYM (@lem1269961 x y x' y')). Qed.
Lemma lem1269965 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) (h1 : term73 x' y' x y) : term73 x' y' x y.
Proof. exact (h1). Qed.
Lemma lem1269966 (y' : nadd) (x : nadd) (y : nadd) (h1 : term72 y' x y) : term72 y' x y.
Proof. exact (h1). Qed.
Lemma lem1269967 (x' : nadd) (x : nadd) (h1 : term70 x' x) : term70 x' x.
Proof. exact (h1). Qed.
Lemma lem1269968 (x' : nadd) (x : nadd) (B1 : nat) (h1 : term67 x' x B1) : term67 x' x B1.
Proof. exact (h1). Qed.
Lemma lem1269969 (y' : nadd) (x : nadd) (y : nadd) (h1 : term72 y' x y) : term72 y' x y.
Proof. exact (h1). Qed.
Lemma lem1269970 (x : nadd) (y : nadd) (h1 : term28 x y) : term28 x y.
Proof. exact (h1). Qed.
Lemma lem1269971 (y' : nadd) (y : nadd) (h1 : term70 y' y) : term70 y' y.
Proof. exact (h1). Qed.
Lemma lem1269972 (y' : nadd) (y : nadd) (B2 : nat) (h1 : term67 y' y B2) : term67 y' y B2.
Proof. exact (h1). Qed.
Lemma lem1269973 (x : nadd) (y : nadd) (h1 : term28 x y) : term28 x y.
Proof. exact (h1). Qed.
Lemma lem1269974 (x : nadd) (y : nadd) (B : nat) (h1 : term64 x y B) : term64 x y B.
Proof. exact (h1). Qed.
Lemma lem1270033 (x' : nadd) (x : nadd) (B1 : nat) (h1 : term67 x' x B1) : term64 x' x B1.
Proof. exact (proj2 (@lem1269968 x' x B1 h1)). Qed.
Lemma lem1270034 (n : nat) (x' : nadd) (x : nadd) (B1 : nat) (h1 : term67 x' x B1) : term54 x' x B1 n.
Proof. exact (@lem1270033 x' x B1 h1 n). Qed.
Lemma lem1270035 (x' : nadd) (x : nadd) (n : nat) (B1 : nat) : (term54 x' x B1 n) = (term55 x' x n B1).
Proof. exact (eq_refl (term54 x' x B1 n)). Qed.
Lemma lem1270036 (n : nat) (x' : nadd) (x : nadd) (B1 : nat) (h1 : term67 x' x B1) : term55 x' x n B1.
Proof. exact (EQ_MP (@lem1270035 x' x n B1) (@lem1270034 n x' x B1 h1)). Qed.
Lemma lem1270037 (h1 : term76) : term76.
Proof. exact (h1). Qed.
Lemma lem1270038 (m : nat) (h1 : term76) : term77 m.
Proof. exact (@lem1270037 h1 m). Qed.
Lemma lem1270039 (m : nat) : (term77 m) = (term78 m).
Proof. exact (eq_refl (term77 m)). Qed.
Lemma lem1270040 (m : nat) (h1 : term76) : term78 m.
Proof. exact (EQ_MP (@lem1270039 m) (@lem1270038 m h1)). Qed.
Lemma lem1270041 (m : nat) (n : nat) (h1 : term76) : term79 m n.
Proof. exact (@lem1270040 m h1 n). Qed.
Lemma lem1270042 (n : nat) (m : nat) : (term79 m n) = (term80 n m).
Proof. exact (eq_refl (term79 m n)). Qed.
Lemma lem1270043 (n : nat) (m : nat) (h1 : term76) : term80 n m.
Proof. exact (EQ_MP (@lem1270042 n m) (@lem1270041 m n h1)). Qed.
Lemma lem1270044 (n : nat) (m : nat) (p : nat) (h1 : term76) : term81 n m p.
Proof. exact (@lem1270043 n m h1 p). Qed.
Lemma lem1270045 (n : nat) (m : nat) (p : nat) : (term81 n m p) = (term82 n m p).
Proof. exact (eq_refl (term81 n m p)). Qed.
Lemma lem1270046 (n : nat) (m : nat) (p : nat) (h1 : term76) : term82 n m p.
Proof. exact (EQ_MP (@lem1270045 n m p) (@lem1270044 n m p h1)). Qed.
Lemma lem1270047 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1270048 (p : nat) (m : nat) (n : nat) (h1 : term76) (h2 : Peano.le m n) : term83 n m p.
Proof. exact (@lem1270046 n m p h1 (@lem1270047 m n h2)). Qed.
Lemma lem1270049 (m : nat) (n : nat) (h1 : term76) (h2 : Peano.le m n) : term84 n m.
Proof. exact (fun p : nat => @lem1270048 p m n h1 h2). Qed.
Lemma lem1270050 (n : nat) (m : nat) (h1 : term76) : term85 n m.
Proof. exact (fun h0 : Peano.le m n => @lem1270049 m n h1 h0). Qed.
Lemma lem1270051 (m : nat) (h1 : term76) : term86 m.
Proof. exact (fun n : nat => @lem1270050 n m h1). Qed.
Lemma lem1270052 (h1 : term76) : term87.
Proof. exact (fun m : nat => @lem1270051 m h1). Qed.
Lemma lem1270053 : term88.
Proof. exact (fun h0 : term76 => @lem1270052 h0). Qed.
Lemma lem1270054 : term87.
Proof. exact (@lem1270053 (@lem272809)). Qed.
Lemma lem1270055 (m : nat) : term89 m.
Proof. exact (@lem1270054 m). Qed.
Lemma lem1270056 (m : nat) : (term89 m) = (term86 m).
Proof. exact (eq_refl (term89 m)). Qed.
Lemma lem1270057 (m : nat) : term86 m.
Proof. exact (EQ_MP (@lem1270056 m) (@lem1270055 m)). Qed.
Lemma lem1270058 (m : nat) (n : nat) : term90 m n.
Proof. exact (@lem1270057 m n). Qed.
Lemma lem1270059 (n : nat) (m : nat) : (term90 m n) = (term85 n m).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem1270062 (n : nat) (m : nat) : term85 n m.
Proof. exact (EQ_MP (@lem1270059 n m) (@lem1270058 m n)). Qed.
Lemma lem1270063 (x : nadd) (B1 : nat) (x' : nadd) (n : nat) : term91 x B1 x' n.
Proof. exact (@lem1270062 (term92 x n B1) (dest_nadd x' n)). Qed.
Lemma lem1270064 (n : nat) (x' : nadd) (x : nadd) (B1 : nat) (h1 : term67 x' x B1) : term93 x B1 x' n.
Proof. exact (@lem1270063 x B1 x' n (@lem1270036 n x' x B1 h1)). Qed.
Lemma lem1270065 (x' : nadd) (x : nadd) (B1 : nat) (h1 : term67 x' x B1) : term94 x B1 x'.
Proof. exact (fun n : nat => @lem1270064 n x' x B1 h1). Qed.
Lemma lem1270066 (x : nadd) (B1 : nat) (x' : nadd) (h1 : term94 x B1 x') : term94 x B1 x'.
Proof. exact (h1). Qed.
Lemma lem1270067 (n : nat) (x : nadd) (B1 : nat) (x' : nadd) (h1 : term94 x B1 x') : term95 x B1 x' n.
Proof. exact (@lem1270066 x B1 x' h1 n). Qed.
Lemma lem1270068 (x : nadd) (B1 : nat) (x' : nadd) (n : nat) : (term95 x B1 x' n) = (term93 x B1 x' n).
Proof. exact (eq_refl (term95 x B1 x' n)). Qed.
Lemma lem1270069 (n : nat) (x : nadd) (B1 : nat) (x' : nadd) (h1 : term94 x B1 x') : term93 x B1 x' n.
Proof. exact (EQ_MP (@lem1270068 x B1 x' n) (@lem1270067 n x B1 x' h1)). Qed.
Lemma lem1270070 (n : nat) (p : nat) (x : nadd) (B1 : nat) (x' : nadd) (h1 : term94 x B1 x') : term96 x B1 x' n p.
Proof. exact (@lem1270069 n x B1 x' h1 p). Qed.
Lemma lem1270071 (x : nadd) (B1 : nat) (x' : nadd) (n : nat) (p : nat) : (term96 x B1 x' n p) = (term97 x B1 x' n p).
Proof. exact (eq_refl (term96 x B1 x' n p)). Qed.
Lemma lem1270072 (n : nat) (p : nat) (x : nadd) (B1 : nat) (x' : nadd) (h1 : term94 x B1 x') : term97 x B1 x' n p.
Proof. exact (EQ_MP (@lem1270071 x B1 x' n p) (@lem1270070 n p x B1 x' h1)). Qed.
Lemma lem1270073 (x : nadd) (n : nat) (B1 : nat) (p : nat) (h1 : term98 x n B1 p) : term98 x n B1 p.
Proof. exact (h1). Qed.
Lemma lem1270074 (x' : nadd) (x : nadd) (n : nat) (B1 : nat) (p : nat) (h1 : term94 x B1 x') (h2 : term98 x n B1 p) : term99 x' n p.
Proof. exact (@lem1270072 n p x B1 x' h1 (@lem1270073 x n B1 p h2)). Qed.
Lemma lem1270075 (x' : nadd) (x : nadd) (n : nat) (B1 : nat) (p : nat) (h1 : term98 x n B1 p) : term100 x B1 x' n p.
Proof. exact (fun h0 : term94 x B1 x' => @lem1270074 x' x n B1 p h0 h1). Qed.
Lemma lem1270076 (x : nadd) (B1 : nat) (x' : nadd) (h1 : term94 x B1 x') : term94 x B1 x'.
Proof. exact (h1). Qed.
Lemma lem1270077 (x' : nadd) (x : nadd) (n : nat) (B1 : nat) (p : nat) (h1 : term94 x B1 x') (h2 : term98 x n B1 p) : term99 x' n p.
Proof. exact (@lem1270075 x' x n B1 p h2 (@lem1270076 x B1 x' h1)). Qed.
Lemma lem1270078 (n : nat) (p : nat) (x : nadd) (B1 : nat) (x' : nadd) (h1 : term94 x B1 x') : term97 x B1 x' n p.
Proof. exact (fun h0 : term98 x n B1 p => @lem1270077 x' x n B1 p h1 h0). Qed.
Lemma lem1270079 (n : nat) (x : nadd) (B1 : nat) (x' : nadd) (h1 : term94 x B1 x') : term93 x B1 x' n.
Proof. exact (fun p : nat => @lem1270078 n p x B1 x' h1). Qed.
Lemma lem1270080 (x : nadd) (B1 : nat) (x' : nadd) (h1 : term94 x B1 x') : term94 x B1 x'.
Proof. exact (fun n : nat => @lem1270079 n x B1 x' h1). Qed.
Lemma lem1270081 (x : nadd) (B1 : nat) (x' : nadd) : term101 x B1 x'.
Proof. exact (fun h0 : term94 x B1 x' => @lem1270080 x B1 x' h0). Qed.
Lemma lem1270082 (x' : nadd) (x : nadd) (B1 : nat) (h1 : term67 x' x B1) : term94 x B1 x'.
Proof. exact (@lem1270081 x B1 x' (@lem1270065 x' x B1 h1)). Qed.
Lemma lem1270083 (n : nat) (x' : nadd) (x : nadd) (B1 : nat) (h1 : term67 x' x B1) : term95 x B1 x' n.
Proof. exact (@lem1270082 x' x B1 h1 n). Qed.
Lemma lem1270084 (x : nadd) (B1 : nat) (x' : nadd) (n : nat) : (term95 x B1 x' n) = (term93 x B1 x' n).
Proof. exact (eq_refl (term95 x B1 x' n)). Qed.
Lemma lem1270085 (n : nat) (x' : nadd) (x : nadd) (B1 : nat) (h1 : term67 x' x B1) : term93 x B1 x' n.
Proof. exact (EQ_MP (@lem1270084 x B1 x' n) (@lem1270083 n x' x B1 h1)). Qed.
Lemma lem1270086 (n : nat) (p : nat) (x' : nadd) (x : nadd) (B1 : nat) (h1 : term67 x' x B1) : term96 x B1 x' n p.
Proof. exact (@lem1270085 n x' x B1 h1 p). Qed.
Lemma lem1270087 (x : nadd) (B1 : nat) (x' : nadd) (n : nat) (p : nat) : (term96 x B1 x' n p) = (term97 x B1 x' n p).
Proof. exact (eq_refl (term96 x B1 x' n p)). Qed.
Lemma lem1270090 (n : nat) (p : nat) (x' : nadd) (x : nadd) (B1 : nat) (h1 : term67 x' x B1) : term97 x B1 x' n p.
Proof. exact (EQ_MP (@lem1270087 x B1 x' n p) (@lem1270086 n p x' x B1 h1)). Qed.
Lemma lem1270091 (y' : nadd) (n : nat) (B2 : nat) (B : nat) (x' : nadd) (x : nadd) (B1 : nat) (h1 : term67 x' x B1) : term102 x x' y' n B2 B B1.
Proof. exact (@lem1270090 n (term103 y' n B2 B B1) x' x B1 h1). Qed.
Lemma lem1270095 (m : nat) (n : nat) (p : nat) : (term11 m n p) = (term12 m n p).
Proof. exact (EQ_MP (@lem1269709 m n p) (@lem1269708 m n p)). Qed.
Lemma lem1270096 (y' : nadd) (n : nat) (B2 : nat) (B : nat) (B1 : nat) : (term103 y' n B2 B B1) = (term104 y' n B2 B B1).
Proof. exact (@lem1270095 (dest_nadd y' n) (Nat.add B2 B) B1). Qed.
Lemma lem1270098 (m : nat) (n : nat) (p : nat) : (term11 m n p) = (term12 m n p).
Proof. exact (EQ_MP (@lem1269709 m n p) (@lem1269708 m n p)). Qed.
Lemma lem1270099 (y' : nadd) (n : nat) (B2 : nat) (B : nat) : (term105 y' n B2 B) = (term106 y' n B2 B).
Proof. exact (@lem1270098 (dest_nadd y' n) B2 B). Qed.
Lemma lem1270100 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1270101 (y' : nadd) (n : nat) (B2 : nat) (B : nat) : (term107 y' n B2 B) = (term108 y' n B2 B).
Proof. exact (MK_COMB (@lem1270100) (@lem1270099 y' n B2 B)). Qed.
Lemma lem1270102 (B1 : nat) : B1 = B1.
Proof. exact (eq_refl B1). Qed.
Lemma lem1270103 (y' : nadd) (n : nat) (B2 : nat) (B : nat) (B1 : nat) : (term104 y' n B2 B B1) = (term109 y' n B2 B B1).
Proof. exact (MK_COMB (@lem1270101 y' n B2 B) (@lem1270102 B1)). Qed.
Lemma lem1270104 (y' : nadd) (n : nat) (B2 : nat) (B : nat) (B1 : nat) : (term103 y' n B2 B B1) = (term109 y' n B2 B B1).
Proof. exact (TRANS (@lem1270096 y' n B2 B B1) (@lem1270103 y' n B2 B B1)). Qed.
Lemma lem1270105 (x : nadd) (n : nat) (B1 : nat) : (term110 x n B1) = (term110 x n B1).
Proof. exact (eq_refl (term110 x n B1)). Qed.
Lemma lem1270106 (x : nadd) (y' : nadd) (n : nat) (B2 : nat) (B : nat) (B1 : nat) : (term111 x y' n B2 B B1) = (term112 x y' n B2 B B1).
Proof. exact (MK_COMB (@lem1270105 x n B1) (@lem1270104 y' n B2 B B1)). Qed.
Lemma lem1270108 (p : nat) (m : nat) (n : nat) : (term5 m n p) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1269700 p m n) (@lem1269699 m n p)). Qed.
Lemma lem1270109 (B1 : nat) (x : nadd) (y' : nadd) (n : nat) (B2 : nat) (B : nat) : (term112 x y' n B2 B B1) = (term113 x y' n B2 B).
Proof. exact (@lem1270108 B1 (dest_nadd x n) (term106 y' n B2 B)). Qed.
Lemma lem1270110 (B1 : nat) (x : nadd) (y' : nadd) (n : nat) (B2 : nat) (B : nat) : (term111 x y' n B2 B B1) = (term113 x y' n B2 B).
Proof. exact (TRANS (@lem1270106 x y' n B2 B B1) (@lem1270109 B1 x y' n B2 B)). Qed.
Lemma lem1270111 (x : nadd) (y' : nadd) (n : nat) (B2 : nat) (B : nat) (B1 : nat) : (term113 x y' n B2 B) = (term111 x y' n B2 B B1).
Proof. exact (SYM (@lem1270110 B1 x y' n B2 B)). Qed.
Lemma lem1270112 (n : nat) (x : nadd) (y : nadd) (B : nat) (h1 : term64 x y B) : term54 x y B n.
Proof. exact (@lem1269974 x y B h1 n). Qed.
Lemma lem1270113 (x : nadd) (y : nadd) (n : nat) (B : nat) : (term54 x y B n) = (term55 x y n B).
Proof. exact (eq_refl (term54 x y B n)). Qed.
Lemma lem1270114 (n : nat) (x : nadd) (y : nadd) (B : nat) (h1 : term64 x y B) : term55 x y n B.
Proof. exact (EQ_MP (@lem1270113 x y n B) (@lem1270112 n x y B h1)). Qed.
Lemma lem1270115 (h1 : term76) : term76.
Proof. exact (h1). Qed.
Lemma lem1270116 (m : nat) (h1 : term76) : term77 m.
Proof. exact (@lem1270115 h1 m). Qed.
Lemma lem1270117 (m : nat) : (term77 m) = (term78 m).
Proof. exact (eq_refl (term77 m)). Qed.
Lemma lem1270118 (m : nat) (h1 : term76) : term78 m.
Proof. exact (EQ_MP (@lem1270117 m) (@lem1270116 m h1)). Qed.
Lemma lem1270119 (m : nat) (n : nat) (h1 : term76) : term79 m n.
Proof. exact (@lem1270118 m h1 n). Qed.
Lemma lem1270120 (n : nat) (m : nat) : (term79 m n) = (term80 n m).
Proof. exact (eq_refl (term79 m n)). Qed.
Lemma lem1270121 (n : nat) (m : nat) (h1 : term76) : term80 n m.
Proof. exact (EQ_MP (@lem1270120 n m) (@lem1270119 m n h1)). Qed.
Lemma lem1270122 (n : nat) (m : nat) (p : nat) (h1 : term76) : term81 n m p.
Proof. exact (@lem1270121 n m h1 p). Qed.
Lemma lem1270123 (n : nat) (m : nat) (p : nat) : (term81 n m p) = (term82 n m p).
Proof. exact (eq_refl (term81 n m p)). Qed.
Lemma lem1270124 (n : nat) (m : nat) (p : nat) (h1 : term76) : term82 n m p.
Proof. exact (EQ_MP (@lem1270123 n m p) (@lem1270122 n m p h1)). Qed.
Lemma lem1270125 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1270126 (p : nat) (m : nat) (n : nat) (h1 : term76) (h2 : Peano.le m n) : term83 n m p.
Proof. exact (@lem1270124 n m p h1 (@lem1270125 m n h2)). Qed.
Lemma lem1270127 (m : nat) (n : nat) (h1 : term76) (h2 : Peano.le m n) : term84 n m.
Proof. exact (fun p : nat => @lem1270126 p m n h1 h2). Qed.
Lemma lem1270128 (n : nat) (m : nat) (h1 : term76) : term85 n m.
Proof. exact (fun h0 : Peano.le m n => @lem1270127 m n h1 h0). Qed.
Lemma lem1270129 (m : nat) (h1 : term76) : term86 m.
Proof. exact (fun n : nat => @lem1270128 n m h1). Qed.
Lemma lem1270130 (h1 : term76) : term87.
Proof. exact (fun m : nat => @lem1270129 m h1). Qed.
Lemma lem1270131 : term88.
Proof. exact (fun h0 : term76 => @lem1270130 h0). Qed.
Lemma lem1270132 : term87.
Proof. exact (@lem1270131 (@lem272809)). Qed.
Lemma lem1270133 (m : nat) : term89 m.
Proof. exact (@lem1270132 m). Qed.
Lemma lem1270134 (m : nat) : (term89 m) = (term86 m).
Proof. exact (eq_refl (term89 m)). Qed.
Lemma lem1270135 (m : nat) : term86 m.
Proof. exact (EQ_MP (@lem1270134 m) (@lem1270133 m)). Qed.
Lemma lem1270136 (m : nat) (n : nat) : term90 m n.
Proof. exact (@lem1270135 m n). Qed.
Lemma lem1270137 (n : nat) (m : nat) : (term90 m n) = (term85 n m).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem1270140 (n : nat) (m : nat) : term85 n m.
Proof. exact (EQ_MP (@lem1270137 n m) (@lem1270136 m n)). Qed.
Lemma lem1270141 (y : nadd) (B : nat) (x : nadd) (n : nat) : term91 y B x n.
Proof. exact (@lem1270140 (term92 y n B) (dest_nadd x n)). Qed.
Lemma lem1270142 (n : nat) (x : nadd) (y : nadd) (B : nat) (h1 : term64 x y B) : term93 y B x n.
Proof. exact (@lem1270141 y B x n (@lem1270114 n x y B h1)). Qed.
Lemma lem1270143 (x : nadd) (y : nadd) (B : nat) (h1 : term64 x y B) : term94 y B x.
Proof. exact (fun n : nat => @lem1270142 n x y B h1). Qed.
Lemma lem1270144 (y : nadd) (B : nat) (x : nadd) (h1 : term94 y B x) : term94 y B x.
Proof. exact (h1). Qed.
Lemma lem1270145 (n : nat) (y : nadd) (B : nat) (x : nadd) (h1 : term94 y B x) : term95 y B x n.
Proof. exact (@lem1270144 y B x h1 n). Qed.
Lemma lem1270146 (y : nadd) (B : nat) (x : nadd) (n : nat) : (term95 y B x n) = (term93 y B x n).
Proof. exact (eq_refl (term95 y B x n)). Qed.
Lemma lem1270147 (n : nat) (y : nadd) (B : nat) (x : nadd) (h1 : term94 y B x) : term93 y B x n.
Proof. exact (EQ_MP (@lem1270146 y B x n) (@lem1270145 n y B x h1)). Qed.
Lemma lem1270148 (n : nat) (p : nat) (y : nadd) (B : nat) (x : nadd) (h1 : term94 y B x) : term96 y B x n p.
Proof. exact (@lem1270147 n y B x h1 p). Qed.
Lemma lem1270149 (y : nadd) (B : nat) (x : nadd) (n : nat) (p : nat) : (term96 y B x n p) = (term97 y B x n p).
Proof. exact (eq_refl (term96 y B x n p)). Qed.
Lemma lem1270150 (n : nat) (p : nat) (y : nadd) (B : nat) (x : nadd) (h1 : term94 y B x) : term97 y B x n p.
Proof. exact (EQ_MP (@lem1270149 y B x n p) (@lem1270148 n p y B x h1)). Qed.
Lemma lem1270151 (y : nadd) (n : nat) (B : nat) (p : nat) (h1 : term98 y n B p) : term98 y n B p.
Proof. exact (h1). Qed.
Lemma lem1270152 (x : nadd) (y : nadd) (n : nat) (B : nat) (p : nat) (h1 : term94 y B x) (h2 : term98 y n B p) : term99 x n p.
Proof. exact (@lem1270150 n p y B x h1 (@lem1270151 y n B p h2)). Qed.
Lemma lem1270153 (x : nadd) (y : nadd) (n : nat) (B : nat) (p : nat) (h1 : term98 y n B p) : term100 y B x n p.
Proof. exact (fun h0 : term94 y B x => @lem1270152 x y n B p h0 h1). Qed.
Lemma lem1270154 (y : nadd) (B : nat) (x : nadd) (h1 : term94 y B x) : term94 y B x.
Proof. exact (h1). Qed.
Lemma lem1270155 (x : nadd) (y : nadd) (n : nat) (B : nat) (p : nat) (h1 : term94 y B x) (h2 : term98 y n B p) : term99 x n p.
Proof. exact (@lem1270153 x y n B p h2 (@lem1270154 y B x h1)). Qed.
Lemma lem1270156 (n : nat) (p : nat) (y : nadd) (B : nat) (x : nadd) (h1 : term94 y B x) : term97 y B x n p.
Proof. exact (fun h0 : term98 y n B p => @lem1270155 x y n B p h1 h0). Qed.
Lemma lem1270157 (n : nat) (y : nadd) (B : nat) (x : nadd) (h1 : term94 y B x) : term93 y B x n.
Proof. exact (fun p : nat => @lem1270156 n p y B x h1). Qed.
Lemma lem1270158 (y : nadd) (B : nat) (x : nadd) (h1 : term94 y B x) : term94 y B x.
Proof. exact (fun n : nat => @lem1270157 n y B x h1). Qed.
Lemma lem1270159 (y : nadd) (B : nat) (x : nadd) : term101 y B x.
Proof. exact (fun h0 : term94 y B x => @lem1270158 y B x h0). Qed.
Lemma lem1270160 (x : nadd) (y : nadd) (B : nat) (h1 : term64 x y B) : term94 y B x.
Proof. exact (@lem1270159 y B x (@lem1270143 x y B h1)). Qed.
Lemma lem1270161 (n : nat) (x : nadd) (y : nadd) (B : nat) (h1 : term64 x y B) : term95 y B x n.
Proof. exact (@lem1270160 x y B h1 n). Qed.
Lemma lem1270162 (y : nadd) (B : nat) (x : nadd) (n : nat) : (term95 y B x n) = (term93 y B x n).
Proof. exact (eq_refl (term95 y B x n)). Qed.
Lemma lem1270163 (n : nat) (x : nadd) (y : nadd) (B : nat) (h1 : term64 x y B) : term93 y B x n.
Proof. exact (EQ_MP (@lem1270162 y B x n) (@lem1270161 n x y B h1)). Qed.
Lemma lem1270164 (n : nat) (p : nat) (x : nadd) (y : nadd) (B : nat) (h1 : term64 x y B) : term96 y B x n p.
Proof. exact (@lem1270163 n x y B h1 p). Qed.
Lemma lem1270165 (y : nadd) (B : nat) (x : nadd) (n : nat) (p : nat) : (term96 y B x n p) = (term97 y B x n p).
Proof. exact (eq_refl (term96 y B x n p)). Qed.
Lemma lem1270168 (n : nat) (p : nat) (x : nadd) (y : nadd) (B : nat) (h1 : term64 x y B) : term97 y B x n p.
Proof. exact (EQ_MP (@lem1270165 y B x n p) (@lem1270164 n p x y B h1)). Qed.
Lemma lem1270169 (y' : nadd) (n : nat) (B2 : nat) (x : nadd) (y : nadd) (B : nat) (h1 : term64 x y B) : term114 y x y' n B2 B.
Proof. exact (@lem1270168 n (term106 y' n B2 B) x y B h1). Qed.
Lemma lem1270170 (m : nat) : term0 m.
Proof. exact (@lem100973 m). Qed.
Lemma lem1270171 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1270172 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1270171 m) (@lem1270170 m)). Qed.
Lemma lem1270173 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1270172 m n). Qed.
Lemma lem1270174 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1270175 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem1270174 m n) (@lem1270173 m n)). Qed.
Lemma lem1270176 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem1270175 m n p). Qed.
Lemma lem1270177 (p : nat) (m : nat) (n : nat) : (term4 m n p) = ((term5 m n p) = (Peano.le m n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem1270197 (y' : nadd) (y : nadd) (B2 : nat) (h1 : term67 y' y B2) : term64 y y' B2.
Proof. exact (proj1 (@lem1269972 y' y B2 h1)). Qed.
Lemma lem1270198 (n : nat) (y' : nadd) (y : nadd) (B2 : nat) (h1 : term67 y' y B2) : term54 y y' B2 n.
Proof. exact (@lem1270197 y' y B2 h1 n). Qed.
Lemma lem1270199 (y : nadd) (y' : nadd) (n : nat) (B2 : nat) : (term54 y y' B2 n) = (term55 y y' n B2).
Proof. exact (eq_refl (term54 y y' B2 n)). Qed.
Lemma lem1270200 (n : nat) (y' : nadd) (y : nadd) (B2 : nat) (h1 : term67 y' y B2) : term55 y y' n B2.
Proof. exact (EQ_MP (@lem1270199 y y' n B2) (@lem1270198 n y' y B2 h1)). Qed.
Lemma lem1270201 (y : nadd) (y' : nadd) (n : nat) (B2 : nat) : (term55 y y' n B2) = ((term55 y y' n B2) = True).
Proof. exact (@lem7 (term55 y y' n B2)). Qed.
Lemma lem1270209 (p : nat) (m : nat) (n : nat) : (term5 m n p) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1270177 p m n) (@lem1270176 m n p)). Qed.
Lemma lem1270210 (B : nat) (y : nadd) (y' : nadd) (n : nat) (B2 : nat) : (term115 y y' n B2 B) = (term55 y y' n B2).
Proof. exact (@lem1270209 B (dest_nadd y n) (term92 y' n B2)). Qed.
Lemma lem1270212 (n : nat) (y' : nadd) (y : nadd) (B2 : nat) (h1 : term67 y' y B2) : (term55 y y' n B2) = True.
Proof. exact (EQ_MP (@lem1270201 y y' n B2) (@lem1270200 n y' y B2 h1)). Qed.
Lemma lem1270213 (n : nat) (B : nat) (y' : nadd) (y : nadd) (B2 : nat) (h1 : term67 y' y B2) : (term115 y y' n B2 B) = True.
Proof. exact (TRANS (@lem1270210 B y y' n B2) (@lem1270212 n y' y B2 h1)). Qed.
Lemma lem1270214 (n : nat) (B : nat) (y' : nadd) (y : nadd) (B2 : nat) (h1 : term67 y' y B2) : True = (term115 y y' n B2 B).
Proof. exact (SYM (@lem1270213 n B y' y B2 h1)). Qed.
Lemma lem1270215 (n : nat) (B : nat) (y' : nadd) (y : nadd) (B2 : nat) (h1 : term67 y' y B2) : term115 y y' n B2 B.
Proof. exact (EQ_MP (@lem1270214 n B y' y B2 h1) (@lem0)). Qed.
Lemma lem1270216 (n : nat) (x : nadd) (B : nat) (y' : nadd) (y : nadd) (B2 : nat) (h1 : term64 x y B) (h2 : term67 y' y B2) : term113 x y' n B2 B.
Proof. exact (@lem1270169 y' n B2 x y B h1 (@lem1270215 n B y' y B2 h2)). Qed.
Lemma lem1270217 (n : nat) (B1 : nat) (x : nadd) (B : nat) (y' : nadd) (y : nadd) (B2 : nat) (h1 : term64 x y B) (h2 : term67 y' y B2) : term111 x y' n B2 B B1.
Proof. exact (EQ_MP (@lem1270111 x y' n B2 B B1) (@lem1270216 n x B y' y B2 h1 h2)). Qed.
Lemma lem1270218 (n : nat) (B : nat) (x' : nadd) (x : nadd) (B1 : nat) (y' : nadd) (y : nadd) (B2 : nat) (h1 : term64 x y B) (h2 : term67 x' x B1) (h3 : term67 y' y B2) : term116 x' y' n B2 B B1.
Proof. exact (@lem1270091 y' n B2 B x' x B1 h2 (@lem1270217 n B1 x B y' y B2 h1 h3)). Qed.
Lemma lem1270223 (B : nat) (x' : nadd) (x : nadd) (B1 : nat) (y' : nadd) (y : nadd) (B2 : nat) (h1 : term64 x y B) (h2 : term67 x' x B1) (h3 : term67 y' y B2) : term117 x' y' B2 B B1.
Proof. exact (fun n : nat => @lem1270218 n B x' x B1 y' y B2 h1 h2 h3). Qed.
Lemma lem1270224 (B : nat) (x' : nadd) (x : nadd) (B1 : nat) (y' : nadd) (y : nadd) (B2 : nat) (h1 : term64 x y B) (h2 : term67 x' x B1) (h3 : term67 y' y B2) : term28 x' y'.
Proof. exact (ex_intro (term118 x' y') (term12 B2 B B1) (@lem1270223 B x' x B1 y' y B2 h1 h2 h3)). Qed.
Lemma lem1270225 (x' : nadd) (x : nadd) (B1 : nat) (y' : nadd) (y : nadd) (B2 : nat) (h1 : term28 x y) (h2 : term67 x' x B1) (h3 : term67 y' y B2) : term28 x' y'.
Proof. exact (ex_elim (@lem1269973 x y h1) (fun B : nat => fun h0 : term118 x y B => @lem1270224 B x' x B1 y' y B2 h0 h2 h3)). Qed.
Lemma lem1270226 (x' : nadd) (x : nadd) (B1 : nat) (y' : nadd) (y : nadd) (B2 : nat) (h1 : term67 x' x B1) (h2 : term67 y' y B2) : term119 x y x' y'.
Proof. exact (fun h0 : term28 x y => @lem1270225 x' x B1 y' y B2 h0 h1 h2). Qed.
Lemma lem1270227 (y' : nadd) (x : nadd) (y : nadd) (h1 : term72 y' x y) : term28 x y.
Proof. exact (proj2 (@lem1269969 y' x y h1)). Qed.
Lemma lem1270228 (y' : nadd) (x : nadd) (y : nadd) (h1 : term72 y' x y) : term70 y' y.
Proof. exact (proj1 (@lem1269969 y' x y h1)). Qed.
Lemma lem1270229 (x' : nadd) (x : nadd) (B1 : nat) (y' : nadd) (y : nadd) (B2 : nat) (h1 : term28 x y) (h2 : term67 x' x B1) (h3 : term67 y' y B2) : term28 x' y'.
Proof. exact (@lem1270226 x' x B1 y' y B2 h2 h3 (@lem1269970 x y h1)). Qed.
Lemma lem1270230 (y' : nadd) (y : nadd) (x' : nadd) (x : nadd) (B1 : nat) (h1 : term28 x y) (h2 : term70 y' y) (h3 : term67 x' x B1) : term28 x' y'.
Proof. exact (ex_elim (@lem1269971 y' y h2) (fun B2 : nat => fun h0 : term69 y' y B2 => @lem1270229 x' x B1 y' y B2 h1 h3 h0)). Qed.
Lemma lem1270231 (x' : nadd) (B1 : nat) (y' : nadd) (x : nadd) (y : nadd) (h1 : term70 y' y) (h2 : term67 x' x B1) (h3 : term72 y' x y) : (term28 x y) = (term28 x' y').
Proof. exact (prop_ext (fun h4 : term28 x y => @lem1270230 y' y x' x B1 h4 h1 h2) (fun h4 : term28 x' y' => @lem1270227 y' x y h3)). Qed.
Lemma lem1270232 (x' : nadd) (B1 : nat) (y' : nadd) (x : nadd) (y : nadd) (h1 : term70 y' y) (h2 : term67 x' x B1) (h3 : term72 y' x y) : term28 x' y'.
Proof. exact (EQ_MP (@lem1270231 x' B1 y' x y h1 h2 h3) (@lem1270227 y' x y h3)). Qed.
Lemma lem1270233 (x' : nadd) (B1 : nat) (y' : nadd) (x : nadd) (y : nadd) (h1 : term67 x' x B1) (h2 : term72 y' x y) : (term70 y' y) = (term28 x' y').
Proof. exact (prop_ext (fun h3 : term70 y' y => @lem1270232 x' B1 y' x y h3 h1 h2) (fun h3 : term28 x' y' => @lem1270228 y' x y h2)). Qed.
Lemma lem1270234 (x' : nadd) (B1 : nat) (y' : nadd) (x : nadd) (y : nadd) (h1 : term67 x' x B1) (h2 : term72 y' x y) : term28 x' y'.
Proof. exact (EQ_MP (@lem1270233 x' B1 y' x y h1 h2) (@lem1270228 y' x y h2)). Qed.
Lemma lem1270235 (y : nadd) (y' : nadd) (x' : nadd) (x : nadd) (B1 : nat) (h1 : term67 x' x B1) : term120 x y x' y'.
Proof. exact (fun h0 : term72 y' x y => @lem1270234 x' B1 y' x y h1 h0). Qed.
Lemma lem1270236 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) (h1 : term73 x' y' x y) : term72 y' x y.
Proof. exact (proj2 (@lem1269965 x' y' x y h1)). Qed.
Lemma lem1270237 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) (h1 : term73 x' y' x y) : term70 x' x.
Proof. exact (proj1 (@lem1269965 x' y' x y h1)). Qed.
Lemma lem1270238 (x' : nadd) (B1 : nat) (y' : nadd) (x : nadd) (y : nadd) (h1 : term67 x' x B1) (h2 : term72 y' x y) : term28 x' y'.
Proof. exact (@lem1270235 y y' x' x B1 h1 (@lem1269966 y' x y h2)). Qed.
Lemma lem1270239 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) (h1 : term70 x' x) (h2 : term72 y' x y) : term28 x' y'.
Proof. exact (ex_elim (@lem1269967 x' x h1) (fun B1 : nat => fun h0 : term69 x' x B1 => @lem1270238 x' B1 y' x y h0 h2)). Qed.
Lemma lem1270240 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) (h1 : term70 x' x) (h2 : term73 x' y' x y) : (term72 y' x y) = (term28 x' y').
Proof. exact (prop_ext (fun h3 : term72 y' x y => @lem1270239 x' y' x y h1 h3) (fun h3 : term28 x' y' => @lem1270236 x' y' x y h2)). Qed.
Lemma lem1270241 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) (h1 : term70 x' x) (h2 : term73 x' y' x y) : term28 x' y'.
Proof. exact (EQ_MP (@lem1270240 x' y' x y h1 h2) (@lem1270236 x' y' x y h2)). Qed.
Lemma lem1270242 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) (h1 : term73 x' y' x y) : (term70 x' x) = (term28 x' y').
Proof. exact (prop_ext (fun h2 : term70 x' x => @lem1270241 x' y' x y h2 h1) (fun h2 : term28 x' y' => @lem1270237 x' y' x y h1)). Qed.
Lemma lem1270243 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) (h1 : term73 x' y' x y) : term28 x' y'.
Proof. exact (EQ_MP (@lem1270242 x' y' x y h1) (@lem1270237 x' y' x y h1)). Qed.
Lemma lem1270244 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : term75 x y x' y'.
Proof. exact (fun h0 : term73 x' y' x y => @lem1270243 x' y' x y h0). Qed.
Lemma lem1270245 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : term42 x y x' y'.
Proof. exact (EQ_MP (@lem1269964 x y x' y') (@lem1270244 x y x' y')). Qed.
Lemma lem1270246 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : term41 x y x' y'.
Proof. exact (EQ_MP (@lem1269802 x y x' y') (@lem1270245 x y x' y')). Qed.
Lemma lem1270251 (x : nadd) (y : nadd) (x' : nadd) : term121 x y x'.
Proof. exact (fun y' : nadd => @lem1270246 x y x' y'). Qed.
Lemma lem1270256 (x : nadd) (x' : nadd) : term122 x x'.
Proof. exact (fun y : nadd => @lem1270251 x y x'). Qed.
Lemma lem1270261 (x : nadd) : term123 x.
Proof. exact (fun x' : nadd => @lem1270256 x x'). Qed.
Lemma lem1270266 : term124.
Proof. exact (fun x : nadd => @lem1270261 x). Qed.
