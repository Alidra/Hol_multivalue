Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_ADD_NUMSEG_term_abbrevs.
Require Import FINITE_NUMSEG_spec.
Require Import NSUM_ADD_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem7040764 (m : nat) : term0 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem7040765 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7040766 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7040765 m) (@lem7040764 m)). Qed.
Lemma lem7040767 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7040766 m n). Qed.
Lemma lem7040768 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7040769 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7040768 m n) (@lem7040767 m n)). Qed.
Lemma lem7040770 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem7040772 {_126729 : Type'} (f : _126729 -> nat) : term4 _126729 f.
Proof. exact (@lem6930477 _126729 f). Qed.
Lemma lem7040773 {_126729 : Type'} (f : _126729 -> nat) : (term4 _126729 f) = (term5 _126729 f).
Proof. exact (eq_refl (term4 _126729 f)). Qed.
Lemma lem7040774 {_126729 : Type'} (f : _126729 -> nat) : term5 _126729 f.
Proof. exact (EQ_MP (@lem7040773 _126729 f) (@lem7040772 _126729 f)). Qed.
Lemma lem7040775 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) : term6 _126729 f g.
Proof. exact (@lem7040774 _126729 f g). Qed.
Lemma lem7040776 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) : (term6 _126729 f g) = (term7 _126729 f g).
Proof. exact (eq_refl (term6 _126729 f g)). Qed.
Lemma lem7040777 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) : term7 _126729 f g.
Proof. exact (EQ_MP (@lem7040776 _126729 f g) (@lem7040775 _126729 f g)). Qed.
Lemma lem7040778 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) (s : _126729 -> Prop) : term8 _126729 f g s.
Proof. exact (@lem7040777 _126729 f g s). Qed.
Lemma lem7040779 {_126729 : Type'} (f : _126729 -> nat) (s : _126729 -> Prop) (g : _126729 -> nat) : (term8 _126729 f g s) = (term9 _126729 f s g).
Proof. exact (eq_refl (term8 _126729 f g s)). Qed.
Lemma lem7040780 {_126729 : Type'} (f : _126729 -> nat) (s : _126729 -> Prop) (g : _126729 -> nat) : term9 _126729 f s g.
Proof. exact (EQ_MP (@lem7040779 _126729 f s g) (@lem7040778 _126729 f g s)). Qed.
Lemma lem7040781 {_126729 : Type'} (s : _126729 -> Prop) (h1 : @FINITE _126729 s) : @FINITE _126729 s.
Proof. exact (h1). Qed.
Lemma lem7040782 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) (s : _126729 -> Prop) (h1 : @FINITE _126729 s) : (term10 _126729 s f g) = (term11 _126729 f s g).
Proof. exact (@lem7040780 _126729 f s g (@lem7040781 _126729 s h1)). Qed.
Lemma lem7040807 {_126729 : Type'} (f : _126729 -> nat) (s : _126729 -> Prop) (g : _126729 -> nat) : term9 _126729 f s g.
Proof. exact (fun h0 : @FINITE _126729 s => @lem7040782 _126729 f g s h0). Qed.
Lemma lem7040808 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : term12 f s g.
Proof. exact (@lem7040807 nat f s g). Qed.
Lemma lem7040809 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : term13 f m n g.
Proof. exact (@lem7040808 f (dotdot m n) g). Qed.
Lemma lem7040811 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem7040770 m n) (@lem7040769 m n)). Qed.
Lemma lem7040812 (m : nat) (n : nat) : True = (term3 m n).
Proof. exact (SYM (@lem7040811 m n)). Qed.
Lemma lem7040813 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7040812 m n) (@lem0)). Qed.
Lemma lem7040814 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : (term14 m n f g) = (term15 f m n g).
Proof. exact (@lem7040809 f m n g (@lem7040813 m n)). Qed.
Lemma lem7040815 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7040816 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : (term16 m n f g) = (term17 f m n g).
Proof. exact (MK_COMB (@lem7040815) (@lem7040814 f m n g)). Qed.
Lemma lem7040817 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : (term15 f m n g) = (term15 f m n g).
Proof. exact (eq_refl (term15 f m n g)). Qed.
Lemma lem7040818 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : ((term14 m n f g) = (term15 f m n g)) = ((term15 f m n g) = (term15 f m n g)).
Proof. exact (MK_COMB (@lem7040816 f m n g) (@lem7040817 f m n g)). Qed.
Lemma lem7040820 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7040821 (x : nat) : (x = x) = True.
Proof. exact (@lem7040820 nat x). Qed.
Lemma lem7040822 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : ((term15 f m n g) = (term15 f m n g)) = True.
Proof. exact (@lem7040821 (term15 f m n g)). Qed.
Lemma lem7040823 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : ((term14 m n f g) = (term15 f m n g)) = True.
Proof. exact (TRANS (@lem7040818 f m n g) (@lem7040822 f m n g)). Qed.
Lemma lem7040824 (f : nat -> nat) (m : nat) (g : nat -> nat) : (term18 f m g) = term19.
Proof. exact (fun_ext (fun n : nat => @lem7040823 f m n g)). Qed.
Lemma lem7040825 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7040826 (f : nat -> nat) (m : nat) (g : nat -> nat) : (term20 f m g) = term21.
Proof. exact (MK_COMB (@lem7040825) (@lem7040824 f m g)). Qed.
Lemma lem7040828 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7040829 (t : Prop) : (term23 t) = t.
Proof. exact (@lem7040828 nat t). Qed.
Lemma lem7040830 : term21 = True.
Proof. exact (@lem7040829 True). Qed.
Lemma lem7040831 (f : nat -> nat) (m : nat) (g : nat -> nat) : (term20 f m g) = True.
Proof. exact (TRANS (@lem7040826 f m g) (@lem7040830)). Qed.
Lemma lem7040832 (f : nat -> nat) (g : nat -> nat) : (term24 f g) = term19.
Proof. exact (fun_ext (fun m : nat => @lem7040831 f m g)). Qed.
Lemma lem7040833 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7040834 (f : nat -> nat) (g : nat -> nat) : (term25 f g) = term21.
Proof. exact (MK_COMB (@lem7040833) (@lem7040832 f g)). Qed.
Lemma lem7040836 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7040837 (t : Prop) : (term23 t) = t.
Proof. exact (@lem7040836 nat t). Qed.
Lemma lem7040838 : term21 = True.
Proof. exact (@lem7040837 True). Qed.
Lemma lem7040839 (f : nat -> nat) (g : nat -> nat) : (term25 f g) = True.
Proof. exact (TRANS (@lem7040834 f g) (@lem7040838)). Qed.
Lemma lem7040840 (f : nat -> nat) : (term26 f) = term27.
Proof. exact (fun_ext (fun g : nat -> nat => @lem7040839 f g)). Qed.
Lemma lem7040841 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7040842 (f : nat -> nat) : (term28 f) = term29.
Proof. exact (MK_COMB (@lem7040841) (@lem7040840 f)). Qed.
Lemma lem7040844 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7040845 (t : Prop) : (term30 t) = t.
Proof. exact (@lem7040844 (nat -> nat) t). Qed.
Lemma lem7040846 : term29 = True.
Proof. exact (@lem7040845 True). Qed.
Lemma lem7040847 (f : nat -> nat) : (term28 f) = True.
Proof. exact (TRANS (@lem7040842 f) (@lem7040846)). Qed.
Lemma lem7040848 : term31 = term27.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7040847 f)). Qed.
Lemma lem7040849 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7040850 : term32 = term29.
Proof. exact (MK_COMB (@lem7040849) (@lem7040848)). Qed.
Lemma lem7040852 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7040853 (t : Prop) : (term30 t) = t.
Proof. exact (@lem7040852 (nat -> nat) t). Qed.
Lemma lem7040854 : term29 = True.
Proof. exact (@lem7040853 True). Qed.
Lemma lem7040855 : term32 = True.
Proof. exact (TRANS (@lem7040850) (@lem7040854)). Qed.
Lemma lem7040856 : True = term32.
Proof. exact (SYM (@lem7040855)). Qed.
Lemma lem7040857 : term32.
Proof. exact (EQ_MP (@lem7040856) (@lem0)). Qed.
