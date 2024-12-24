Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_ABS_NUMSEG_term_abbrevs.
Require Import FINITE_NUMSEG_spec.
Require Import SUM_ABS_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem7213671 (m : nat) : term0 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem7213672 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7213673 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7213672 m) (@lem7213671 m)). Qed.
Lemma lem7213674 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7213673 m n). Qed.
Lemma lem7213675 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7213676 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7213675 m n) (@lem7213674 m n)). Qed.
Lemma lem7213677 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem7213679 {_132408 : Type'} (f : _132408 -> real) : term4 _132408 f.
Proof. exact (@lem7083749 _132408 f). Qed.
Lemma lem7213680 {_132408 : Type'} (f : _132408 -> real) : (term4 _132408 f) = (term5 _132408 f).
Proof. exact (eq_refl (term4 _132408 f)). Qed.
Lemma lem7213681 {_132408 : Type'} (f : _132408 -> real) : term5 _132408 f.
Proof. exact (EQ_MP (@lem7213680 _132408 f) (@lem7213679 _132408 f)). Qed.
Lemma lem7213682 {_132408 : Type'} (f : _132408 -> real) (s : _132408 -> Prop) : term6 _132408 f s.
Proof. exact (@lem7213681 _132408 f s). Qed.
Lemma lem7213683 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : (term6 _132408 f s) = (term7 _132408 s f).
Proof. exact (eq_refl (term6 _132408 f s)). Qed.
Lemma lem7213684 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : term7 _132408 s f.
Proof. exact (EQ_MP (@lem7213683 _132408 s f) (@lem7213682 _132408 f s)). Qed.
Lemma lem7213685 {_132408 : Type'} (s : _132408 -> Prop) (h1 : @FINITE _132408 s) : @FINITE _132408 s.
Proof. exact (h1). Qed.
Lemma lem7213686 {_132408 : Type'} (f : _132408 -> real) (s : _132408 -> Prop) (h1 : @FINITE _132408 s) : term8 _132408 s f.
Proof. exact (@lem7213684 _132408 s f (@lem7213685 _132408 s h1)). Qed.
Lemma lem7213687 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : (term8 _132408 s f) = ((term8 _132408 s f) = True).
Proof. exact (@lem7 (term8 _132408 s f)). Qed.
Lemma lem7213688 {_132408 : Type'} (f : _132408 -> real) (s : _132408 -> Prop) (h1 : @FINITE _132408 s) : (term8 _132408 s f) = True.
Proof. exact (EQ_MP (@lem7213687 _132408 s f) (@lem7213686 _132408 f s h1)). Qed.
Lemma lem7213707 {_132408 : Type'} (s : _132408 -> Prop) (f : _132408 -> real) : term9 _132408 s f.
Proof. exact (fun h0 : @FINITE _132408 s => @lem7213688 _132408 f s h0). Qed.
Lemma lem7213708 (s : nat -> Prop) (f : nat -> real) : term10 s f.
Proof. exact (@lem7213707 nat s f). Qed.
Lemma lem7213709 (m : nat) (n : nat) (f : nat -> real) : term11 m n f.
Proof. exact (@lem7213708 (dotdot m n) f). Qed.
Lemma lem7213711 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem7213677 m n) (@lem7213676 m n)). Qed.
Lemma lem7213712 (m : nat) (n : nat) : True = (term3 m n).
Proof. exact (SYM (@lem7213711 m n)). Qed.
Lemma lem7213713 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7213712 m n) (@lem0)). Qed.
Lemma lem7213714 (m : nat) (n : nat) (f : nat -> real) : (term12 m n f) = True.
Proof. exact (@lem7213709 m n f (@lem7213713 m n)). Qed.
Lemma lem7213715 (m : nat) (f : nat -> real) : (term13 m f) = term14.
Proof. exact (fun_ext (fun n : nat => @lem7213714 m n f)). Qed.
Lemma lem7213716 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7213717 (m : nat) (f : nat -> real) : (term15 m f) = term16.
Proof. exact (MK_COMB (@lem7213716) (@lem7213715 m f)). Qed.
Lemma lem7213719 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7213720 (t : Prop) : (term18 t) = t.
Proof. exact (@lem7213719 nat t). Qed.
Lemma lem7213721 : term16 = True.
Proof. exact (@lem7213720 True). Qed.
Lemma lem7213722 (m : nat) (f : nat -> real) : (term15 m f) = True.
Proof. exact (TRANS (@lem7213717 m f) (@lem7213721)). Qed.
Lemma lem7213723 (f : nat -> real) : (term19 f) = term14.
Proof. exact (fun_ext (fun m : nat => @lem7213722 m f)). Qed.
Lemma lem7213724 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7213725 (f : nat -> real) : (term20 f) = term16.
Proof. exact (MK_COMB (@lem7213724) (@lem7213723 f)). Qed.
Lemma lem7213727 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7213728 (t : Prop) : (term18 t) = t.
Proof. exact (@lem7213727 nat t). Qed.
Lemma lem7213729 : term16 = True.
Proof. exact (@lem7213728 True). Qed.
Lemma lem7213730 (f : nat -> real) : (term20 f) = True.
Proof. exact (TRANS (@lem7213725 f) (@lem7213729)). Qed.
Lemma lem7213731 : term21 = term22.
Proof. exact (fun_ext (fun f : nat -> real => @lem7213730 f)). Qed.
Lemma lem7213732 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7213733 : term23 = term24.
Proof. exact (MK_COMB (@lem7213732) (@lem7213731)). Qed.
Lemma lem7213735 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7213736 (t : Prop) : (term25 t) = t.
Proof. exact (@lem7213735 (nat -> real) t). Qed.
Lemma lem7213737 : term24 = True.
Proof. exact (@lem7213736 True). Qed.
Lemma lem7213738 : term23 = True.
Proof. exact (TRANS (@lem7213733) (@lem7213737)). Qed.
Lemma lem7213739 : True = term23.
Proof. exact (SYM (@lem7213738)). Qed.
Lemma lem7213740 : term23.
Proof. exact (EQ_MP (@lem7213739) (@lem0)). Qed.
