Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_POWERSET_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import CONTRAPOS_THM_spec.
Require Import EXTENSION_spec.
Require Import HAS_SIZE_CLAUSES_spec.
Require Import HAS_SIZE_FUNSPACE_spec.
Require Import IN_spec.
Require Import IN_INSERT_spec.
Require Import IN_UNIV_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import SUBSET_spec.
Require Import thm0_spec.
Require Import thm1005477_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3888988_spec.
Require Import thm3892933_spec.
Require Import thm3892937_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm912741_spec.
Lemma lem4596662 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4596663 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem4596664 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem4596663 A x) (@lem4596662 A x)). Qed.
Lemma lem4596665 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4596667 {A : Type'} (x : A) : term3 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem4596668 {A : Type'} (x : A) : (term3 A x) = (term4 A x).
Proof. exact (eq_refl (term3 A x)). Qed.
Lemma lem4596669 {A : Type'} (x : A) : term4 A x.
Proof. exact (EQ_MP (@lem4596668 A x) (@lem4596667 A x)). Qed.
Lemma lem4596670 {A : Type'} (x : A) (y : A) : term5 A x y.
Proof. exact (@lem4596669 A x y). Qed.
Lemma lem4596671 {A : Type'} (y : A) (x : A) : (term5 A x y) = (term6 A y x).
Proof. exact (eq_refl (term5 A x y)). Qed.
Lemma lem4596672 {A : Type'} (y : A) (x : A) : term6 A y x.
Proof. exact (EQ_MP (@lem4596671 A y x) (@lem4596670 A x y)). Qed.
Lemma lem4596673 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term7 A y x s.
Proof. exact (@lem4596672 A y x s). Qed.
Lemma lem4596674 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term7 A y x s) = ((term8 A x y s) = (term9 A y x s)).
Proof. exact (eq_refl (term7 A y x s)). Qed.
Lemma lem4596676 {A : Type'} (x : A) : term10 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem4596677 {A : Type'} (x : A) : (term10 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term10 A x)). Qed.
Lemma lem4596678 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem4596677 A x) (@lem4596676 A x)). Qed.
Lemma lem4596679 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem4596681 {A : Type'} (s : A -> Prop) : term11 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4596682 {A : Type'} (s : A -> Prop) : (term11 A s) = (term12 A s).
Proof. exact (eq_refl (term11 A s)). Qed.
Lemma lem4596683 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (EQ_MP (@lem4596682 A s) (@lem4596681 A s)). Qed.
Lemma lem4596684 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term13 A s t.
Proof. exact (@lem4596683 A s t). Qed.
Lemma lem4596685 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term13 A s t) = ((s = t) = (term14 A s t)).
Proof. exact (eq_refl (term13 A s t)). Qed.
Lemma lem4596687 {A B : Type'} (h1 : term15 A B) : term15 A B.
Proof. exact (h1). Qed.
Lemma lem4596688 {A B : Type'} (d : B) (h1 : term15 A B) : term16 A B d.
Proof. exact (@lem4596687 A B h1 d). Qed.
Lemma lem4596689 {A B : Type'} (d : B) : (term16 A B d) = (term17 A B d).
Proof. exact (eq_refl (term16 A B d)). Qed.
Lemma lem4596690 {A B : Type'} (d : B) (h1 : term15 A B) : term17 A B d.
Proof. exact (EQ_MP (@lem4596689 A B d) (@lem4596688 A B d h1)). Qed.
Lemma lem4596691 {A B : Type'} (d : B) (n : nat) (h1 : term15 A B) : term18 A B d n.
Proof. exact (@lem4596690 A B d h1 n). Qed.
Lemma lem4596692 {A B : Type'} (d : B) (n : nat) : (term18 A B d n) = (term19 A B d n).
Proof. exact (eq_refl (term18 A B d n)). Qed.
Lemma lem4596693 {A B : Type'} (d : B) (n : nat) (h1 : term15 A B) : term19 A B d n.
Proof. exact (EQ_MP (@lem4596692 A B d n) (@lem4596691 A B d n h1)). Qed.
Lemma lem4596694 {A B : Type'} (d : B) (n : nat) (t : B -> Prop) (h1 : term15 A B) : term20 A B d n t.
Proof. exact (@lem4596693 A B d n h1 t). Qed.
Lemma lem4596695 {A B : Type'} (t : B -> Prop) (d : B) (n : nat) : (term20 A B d n t) = (term21 A B t d n).
Proof. exact (eq_refl (term20 A B d n t)). Qed.
Lemma lem4596696 {A B : Type'} (t : B -> Prop) (d : B) (n : nat) (h1 : term15 A B) : term21 A B t d n.
Proof. exact (EQ_MP (@lem4596695 A B t d n) (@lem4596694 A B d n t h1)). Qed.
Lemma lem4596697 {A B : Type'} (t : B -> Prop) (d : B) (n : nat) (m : nat) (h1 : term15 A B) : term22 A B t d n m.
Proof. exact (@lem4596696 A B t d n h1 m). Qed.
Lemma lem4596698 {A B : Type'} (t : B -> Prop) (d : B) (n : nat) (m : nat) : (term22 A B t d n m) = (term23 A B t d n m).
Proof. exact (eq_refl (term22 A B t d n m)). Qed.
Lemma lem4596699 {A B : Type'} (t : B -> Prop) (d : B) (n : nat) (m : nat) (h1 : term15 A B) : term23 A B t d n m.
Proof. exact (EQ_MP (@lem4596698 A B t d n m) (@lem4596697 A B t d n m h1)). Qed.
Lemma lem4596700 {A B : Type'} (t : B -> Prop) (d : B) (n : nat) (m : nat) (s : A -> Prop) (h1 : term15 A B) : term24 A B t d n m s.
Proof. exact (@lem4596699 A B t d n m h1 s). Qed.
Lemma lem4596701 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (d : B) (n : nat) (m : nat) : (term24 A B t d n m s) = (term25 A B t s d n m).
Proof. exact (eq_refl (term24 A B t d n m s)). Qed.
Lemma lem4596702 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (d : B) (n : nat) (m : nat) (h1 : term15 A B) : term25 A B t s d n m.
Proof. exact (EQ_MP (@lem4596701 A B t s d n m) (@lem4596700 A B t d n m s h1)). Qed.
Lemma lem4596703 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term26 A B s m t n) : term26 A B s m t n.
Proof. exact (h1). Qed.
Lemma lem4596704 {A B : Type'} (d : B) (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term15 A B) (h2 : term26 A B s m t n) : term27 A B t s d n m.
Proof. exact (@lem4596702 A B t s d n m h1 (@lem4596703 A B s m t n h2)). Qed.
Lemma lem4596705 {A B : Type'} (d : B) (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term26 A B s m t n) : term28 A B t s d n m.
Proof. exact (fun h0 : term15 A B => @lem4596704 A B d s m t n h0 h1). Qed.
Lemma lem4596706 {A B : Type'} (h1 : term15 A B) : term15 A B.
Proof. exact (h1). Qed.
Lemma lem4596707 {A B : Type'} (d : B) (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term15 A B) (h2 : term26 A B s m t n) : term27 A B t s d n m.
Proof. exact (@lem4596705 A B d s m t n h2 (@lem4596706 A B h1)). Qed.
Lemma lem4596708 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (d : B) (n : nat) (m : nat) (h1 : term15 A B) : term25 A B t s d n m.
Proof. exact (fun h0 : term26 A B s m t n => @lem4596707 A B d s m t n h1 h0). Qed.
Lemma lem4596709 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (d : B) (n : nat) (h1 : term15 A B) : term29 A B t s d n.
Proof. exact (fun m : nat => @lem4596708 A B t s d n m h1). Qed.
Lemma lem4596710 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (d : B) (h1 : term15 A B) : term30 A B t s d.
Proof. exact (fun n : nat => @lem4596709 A B t s d n h1). Qed.
Lemma lem4596711 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term15 A B) : term31 A B t s.
Proof. exact (fun d : B => @lem4596710 A B t s d h1). Qed.
Lemma lem4596712 {A B : Type'} (t : B -> Prop) (h1 : term15 A B) : term32 A B t.
Proof. exact (fun s : A -> Prop => @lem4596711 A B t s h1). Qed.
Lemma lem4596713 {A B : Type'} (h1 : term15 A B) : term33 A B.
Proof. exact (fun t : B -> Prop => @lem4596712 A B t h1). Qed.
Lemma lem4596714 {A B : Type'} : term34 A B.
Proof. exact (fun h0 : term15 A B => @lem4596713 A B h0). Qed.
Lemma lem4596715 {A B : Type'} : term33 A B.
Proof. exact (@lem4596714 A B (@lem4521678 A B)). Qed.
Lemma lem4596716 {A B : Type'} (t : B -> Prop) : term35 A B t.
Proof. exact (@lem4596715 A B t). Qed.
Lemma lem4596717 {A B : Type'} (t : B -> Prop) : (term35 A B t) = (term32 A B t).
Proof. exact (eq_refl (term35 A B t)). Qed.
Lemma lem4596718 {A B : Type'} (t : B -> Prop) : term32 A B t.
Proof. exact (EQ_MP (@lem4596717 A B t) (@lem4596716 A B t)). Qed.
Lemma lem4596719 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term36 A B t s.
Proof. exact (@lem4596718 A B t s). Qed.
Lemma lem4596720 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term36 A B t s) = (term31 A B t s).
Proof. exact (eq_refl (term36 A B t s)). Qed.
Lemma lem4596721 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term31 A B t s.
Proof. exact (EQ_MP (@lem4596720 A B t s) (@lem4596719 A B t s)). Qed.
Lemma lem4596722 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (d : B) : term37 A B t s d.
Proof. exact (@lem4596721 A B t s d). Qed.
Lemma lem4596723 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (d : B) : (term37 A B t s d) = (term30 A B t s d).
Proof. exact (eq_refl (term37 A B t s d)). Qed.
Lemma lem4596724 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (d : B) : term30 A B t s d.
Proof. exact (EQ_MP (@lem4596723 A B t s d) (@lem4596722 A B t s d)). Qed.
Lemma lem4596725 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (d : B) (n : nat) : term38 A B t s d n.
Proof. exact (@lem4596724 A B t s d n). Qed.
Lemma lem4596726 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (d : B) (n : nat) : (term38 A B t s d n) = (term29 A B t s d n).
Proof. exact (eq_refl (term38 A B t s d n)). Qed.
Lemma lem4596727 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (d : B) (n : nat) : term29 A B t s d n.
Proof. exact (EQ_MP (@lem4596726 A B t s d n) (@lem4596725 A B t s d n)). Qed.
Lemma lem4596728 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (d : B) (n : nat) (m : nat) : term39 A B t s d n m.
Proof. exact (@lem4596727 A B t s d n m). Qed.
Lemma lem4596729 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (d : B) (n : nat) (m : nat) : (term39 A B t s d n m) = (term25 A B t s d n m).
Proof. exact (eq_refl (term39 A B t s d n m)). Qed.
Lemma lem4596731 (t1 : Prop) : term40 t1.
Proof. exact (@lem10414 t1). Qed.
Lemma lem4596732 (t1 : Prop) : (term40 t1) = (term41 t1).
Proof. exact (eq_refl (term40 t1)). Qed.
Lemma lem4596733 (t1 : Prop) : term41 t1.
Proof. exact (EQ_MP (@lem4596732 t1) (@lem4596731 t1)). Qed.
Lemma lem4596734 (t1 : Prop) (t2 : Prop) : term42 t1 t2.
Proof. exact (@lem4596733 t1 t2). Qed.
Lemma lem4596735 (t2 : Prop) (t1 : Prop) : (term42 t1 t2) = ((term43 t1 t2) = (t2 -> t1)).
Proof. exact (eq_refl (term42 t1 t2)). Qed.
Lemma lem4596737 {A : Type'} (P : A -> Prop) : term44 A P.
Proof. exact (@lem3181151 A P). Qed.
Lemma lem4596738 {A : Type'} (P : A -> Prop) : (term44 A P) = (term45 A P).
Proof. exact (eq_refl (term44 A P)). Qed.
Lemma lem4596739 {A : Type'} (P : A -> Prop) : term45 A P.
Proof. exact (EQ_MP (@lem4596738 A P) (@lem4596737 A P)). Qed.
Lemma lem4596740 {A : Type'} (P : A -> Prop) (x : A) : term46 A P x.
Proof. exact (@lem4596739 A P x). Qed.
Lemma lem4596741 {A : Type'} (P : A -> Prop) (x : A) : (term46 A P x) = ((@IN A x P) = (P x)).
Proof. exact (eq_refl (term46 A P x)). Qed.
Lemma lem4596743 {A : Type'} (s : A -> Prop) : term47 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem4596744 {A : Type'} (s : A -> Prop) : (term47 A s) = (term48 A s).
Proof. exact (eq_refl (term47 A s)). Qed.
Lemma lem4596745 {A : Type'} (s : A -> Prop) : term48 A s.
Proof. exact (EQ_MP (@lem4596744 A s) (@lem4596743 A s)). Qed.
Lemma lem4596746 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term49 A s t.
Proof. exact (@lem4596745 A s t). Qed.
Lemma lem4596747 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term49 A s t) = ((@SUBSET A s t) = (term50 A s t)).
Proof. exact (eq_refl (term49 A s t)). Qed.
Lemma lem4596749 {A : Type'} (x : A) : term10 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem4596750 {A : Type'} (x : A) : (term10 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term10 A x)). Qed.
Lemma lem4596751 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem4596750 A x) (@lem4596749 A x)). Qed.
Lemma lem4596752 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem4596778 {_83095 : Type'} : term51 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4596779 {_83095 : Type'} (p : _83095 -> Prop) : term52 _83095 p.
Proof. exact (@lem4596778 _83095 p). Qed.
Lemma lem4596780 {_83095 : Type'} (p : _83095 -> Prop) : (term52 _83095 p) = (term53 _83095 p).
Proof. exact (eq_refl (term52 _83095 p)). Qed.
Lemma lem4596781 {_83095 : Type'} (p : _83095 -> Prop) : term53 _83095 p.
Proof. exact (EQ_MP (@lem4596780 _83095 p) (@lem4596779 _83095 p)). Qed.
Lemma lem4596782 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term54 _83095 p x.
Proof. exact (@lem4596781 _83095 p x). Qed.
Lemma lem4596783 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term54 _83095 p x) = ((term55 _83095 x p) = (p x)).
Proof. exact (eq_refl (term54 _83095 p x)). Qed.
Lemma lem4596792 {A : Type'} (s : A -> Prop) : term11 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4596793 {A : Type'} (s : A -> Prop) : (term11 A s) = (term12 A s).
Proof. exact (eq_refl (term11 A s)). Qed.
Lemma lem4596794 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (EQ_MP (@lem4596793 A s) (@lem4596792 A s)). Qed.
Lemma lem4596795 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term13 A s t.
Proof. exact (@lem4596794 A s t). Qed.
Lemma lem4596796 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term13 A s t) = ((s = t) = (term14 A s t)).
Proof. exact (eq_refl (term13 A s t)). Qed.
Lemma lem4596798 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : @HAS_SIZE A s n.
Proof. exact (h1). Qed.
Lemma lem4596799 {A : Type'} (s : A -> Prop) (h1 : (term56 A s) = (term57 A s)) : (term56 A s) = (term57 A s).
Proof. exact (h1). Qed.
Lemma lem4596800 {A : Type'} (n : nat) : (term58 A n) = (term58 A n).
Proof. exact (eq_refl (term58 A n)). Qed.
Lemma lem4596801 {A : Type'} (n : nat) (s : A -> Prop) (h1 : (term56 A s) = (term57 A s)) : (term59 A n s) = (term60 A n s).
Proof. exact (MK_COMB (@lem4596800 A n) (@lem4596799 A s h1)). Qed.
Lemma lem4596802 {A : Type'} (s : A -> Prop) (n : nat) : (term60 A n s) = (term61 A s n).
Proof. exact (eq_refl (term60 A n s)). Qed.
Lemma lem4596803 {A : Type'} (n : nat) (s : A -> Prop) : (term62 A n s) = (term62 A n s).
Proof. exact (eq_refl (term62 A n s)). Qed.
Lemma lem4596804 {A : Type'} (s : A -> Prop) (n : nat) : ((term59 A n s) = (term60 A n s)) = ((term59 A n s) = (term61 A s n)).
Proof. exact (MK_COMB (@lem4596803 A n s) (@lem4596802 A s n)). Qed.
Lemma lem4596805 {A : Type'} (s : A -> Prop) (n : nat) : (term59 A n s) = (term63 A s n).
Proof. exact (eq_refl (term59 A n s)). Qed.
Lemma lem4596806 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4596807 {A : Type'} (s : A -> Prop) (n : nat) : (term62 A n s) = (term64 A s n).
Proof. exact (MK_COMB (@lem4596806) (@lem4596805 A s n)). Qed.
Lemma lem4596808 {A : Type'} (s : A -> Prop) (n : nat) : (term61 A s n) = (term61 A s n).
Proof. exact (eq_refl (term61 A s n)). Qed.
Lemma lem4596809 {A : Type'} (s : A -> Prop) (n : nat) : ((term59 A n s) = (term61 A s n)) = ((term63 A s n) = (term61 A s n)).
Proof. exact (MK_COMB (@lem4596807 A s n) (@lem4596808 A s n)). Qed.
Lemma lem4596810 {A : Type'} (s : A -> Prop) (n : nat) : ((term59 A n s) = (term60 A n s)) = ((term63 A s n) = (term61 A s n)).
Proof. exact (TRANS (@lem4596804 A s n) (@lem4596809 A s n)). Qed.
Lemma lem4596811 {A : Type'} (n : nat) (s : A -> Prop) (h1 : (term56 A s) = (term57 A s)) : (term63 A s n) = (term61 A s n).
Proof. exact (EQ_MP (@lem4596810 A s n) (@lem4596801 A n s h1)). Qed.
Lemma lem4596812 {A : Type'} (n : nat) (s : A -> Prop) (h1 : (term56 A s) = (term57 A s)) : (term61 A s n) = (term63 A s n).
Proof. exact (SYM (@lem4596811 A n s h1)). Qed.
Lemma lem4596816 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term14 A s t).
Proof. exact (EQ_MP (@lem4596796 A s t) (@lem4596795 A s t)). Qed.
Lemma lem4596817 {A : Type'} (s : type686 A) (t : type686 A) : (s = t) = (term65 A s t).
Proof. exact (@lem4596816 (A -> Prop) s t). Qed.
Lemma lem4596818 {A : Type'} (s : A -> Prop) : ((term56 A s) = (term57 A s)) = (term66 A s).
Proof. exact (@lem4596817 A (term56 A s) (term57 A s)). Qed.
Lemma lem4596828 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term55 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4596783 _83095 p x) (@lem4596782 _83095 p x)). Qed.
Lemma lem4596829 {A : Type'} (p : type686 A) (x : A -> Prop) : (term67 A x p) = (p x).
Proof. exact (@lem4596828 (A -> Prop) p x). Qed.
Lemma lem4596830 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term68 A x s) = (term69 A s x).
Proof. exact (@lem4596829 A (term70 A s) x). Qed.
Lemma lem4596831 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term69 A s t) = (@SUBSET A t s).
Proof. exact (eq_refl (term69 A s t)). Qed.
Lemma lem4596832 {A : Type'} (GEN_PVAR_151 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_151) = (@SETSPEC (A -> Prop) GEN_PVAR_151).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_151)). Qed.
Lemma lem4596833 {A : Type'} (GEN_PVAR_151 : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term71 A GEN_PVAR_151 s t) = (term72 A GEN_PVAR_151 t s).
Proof. exact (MK_COMB (@lem4596832 A GEN_PVAR_151) (@lem4596831 A t s)). Qed.
Lemma lem4596834 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4596835 {A : Type'} (GEN_PVAR_151 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term73 A GEN_PVAR_151 s t) = (term74 A GEN_PVAR_151 s t).
Proof. exact (MK_COMB (@lem4596833 A GEN_PVAR_151 t s) (@lem4596834 A t)). Qed.
Lemma lem4596836 {A : Type'} (GEN_PVAR_151 : A -> Prop) (s : A -> Prop) : (term75 A GEN_PVAR_151 s) = (term76 A GEN_PVAR_151 s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4596835 A GEN_PVAR_151 s t)). Qed.
Lemma lem4596837 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4596838 {A : Type'} (GEN_PVAR_151 : A -> Prop) (s : A -> Prop) : (term77 A GEN_PVAR_151 s) = (term78 A GEN_PVAR_151 s).
Proof. exact (MK_COMB (@lem4596837 A) (@lem4596836 A GEN_PVAR_151 s)). Qed.
Lemma lem4596839 {A : Type'} (s : A -> Prop) : (term79 A s) = (term80 A s).
Proof. exact (fun_ext (fun GEN_PVAR_151 : A -> Prop => @lem4596838 A GEN_PVAR_151 s)). Qed.
Lemma lem4596840 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4596841 {A : Type'} (s : A -> Prop) : (term81 A s) = (term56 A s).
Proof. exact (MK_COMB (@lem4596840 A) (@lem4596839 A s)). Qed.
Lemma lem4596842 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x) = (@IN (A -> Prop) x).
Proof. exact (eq_refl (@IN (A -> Prop) x)). Qed.
Lemma lem4596843 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term68 A x s) = (term82 A x s).
Proof. exact (MK_COMB (@lem4596842 A x) (@lem4596841 A s)). Qed.
Lemma lem4596844 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4596845 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term83 A x s) = (term84 A x s).
Proof. exact (MK_COMB (@lem4596844) (@lem4596843 A x s)). Qed.
Lemma lem4596846 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term69 A s x) = (@SUBSET A x s).
Proof. exact (eq_refl (term69 A s x)). Qed.
Lemma lem4596847 {A : Type'} (x : A -> Prop) (s : A -> Prop) : ((term68 A x s) = (term69 A s x)) = ((term82 A x s) = (@SUBSET A x s)).
Proof. exact (MK_COMB (@lem4596845 A x s) (@lem4596846 A x s)). Qed.
Lemma lem4596848 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term82 A x s) = (@SUBSET A x s).
Proof. exact (EQ_MP (@lem4596847 A x s) (@lem4596830 A s x)). Qed.
Lemma lem4596850 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term50 A s t).
Proof. exact (EQ_MP (@lem4596747 A s t) (@lem4596746 A s t)). Qed.
Lemma lem4596851 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term50 A s t).
Proof. exact (@lem4596850 A s t). Qed.
Lemma lem4596852 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (@SUBSET A x s) = (term50 A x s).
Proof. exact (@lem4596851 A x s). Qed.
Lemma lem4596857 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term82 A x s) = (term50 A x s).
Proof. exact (TRANS (@lem4596848 A x s) (@lem4596852 A x s)). Qed.
Lemma lem4596861 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem4596741 A P x) (@lem4596740 A P x)). Qed.
Lemma lem4596862 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4596861 A P x). Qed.
Lemma lem4596863 {A : Type'} (x : A -> Prop) (x' : A) : (@IN A x' x) = (x x').
Proof. exact (@lem4596862 A x x'). Qed.
Lemma lem4596864 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4596865 {A : Type'} (x : A -> Prop) (x' : A) : (term85 A x' x) = (term86 A x x').
Proof. exact (MK_COMB (@lem4596864) (@lem4596863 A x x')). Qed.
Lemma lem4596867 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem4596741 A P x) (@lem4596740 A P x)). Qed.
Lemma lem4596868 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4596867 A P x). Qed.
Lemma lem4596869 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4596868 A s x). Qed.
Lemma lem4596870 {A : Type'} (x : A -> Prop) (s : A -> Prop) (x' : A) : (term87 A x x' s) = (term88 A x s x').
Proof. exact (MK_COMB (@lem4596865 A x x') (@lem4596869 A s x')). Qed.
Lemma lem4596873 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term89 A x s) = (term90 A x s).
Proof. exact (fun_ext (fun x' : A => @lem4596870 A x s x')). Qed.
Lemma lem4596874 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4596875 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term50 A x s) = (term91 A x s).
Proof. exact (MK_COMB (@lem4596874 A) (@lem4596873 A x s)). Qed.
Lemma lem4596880 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term82 A x s) = (term91 A x s).
Proof. exact (TRANS (@lem4596857 A x s) (@lem4596875 A x s)). Qed.
Lemma lem4596881 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4596882 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term84 A x s) = (term92 A x s).
Proof. exact (MK_COMB (@lem4596881) (@lem4596880 A x s)). Qed.
Lemma lem4596884 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term55 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4596783 _83095 p x) (@lem4596782 _83095 p x)). Qed.
Lemma lem4596885 {A : Type'} (p : type686 A) (x : A -> Prop) : (term67 A x p) = (p x).
Proof. exact (@lem4596884 (A -> Prop) p x). Qed.
Lemma lem4596886 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term93 A x s) = (term94 A s x).
Proof. exact (@lem4596885 A (term95 A s) x). Qed.
Lemma lem4596887 {A : Type'} (s : A -> Prop) (f : A -> Prop) : (term94 A s f) = (term96 A s f).
Proof. exact (eq_refl (term94 A s f)). Qed.
Lemma lem4596888 {A : Type'} (GEN_PVAR_152 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_152) = (@SETSPEC (A -> Prop) GEN_PVAR_152).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_152)). Qed.
Lemma lem4596889 {A : Type'} (GEN_PVAR_152 : A -> Prop) (s : A -> Prop) (f : A -> Prop) : (term97 A GEN_PVAR_152 s f) = (term98 A GEN_PVAR_152 s f).
Proof. exact (MK_COMB (@lem4596888 A GEN_PVAR_152) (@lem4596887 A s f)). Qed.
Lemma lem4596890 {A : Type'} (f : A -> Prop) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4596891 {A : Type'} (GEN_PVAR_152 : A -> Prop) (s : A -> Prop) (f : A -> Prop) : (term99 A GEN_PVAR_152 s f) = (term100 A GEN_PVAR_152 s f).
Proof. exact (MK_COMB (@lem4596889 A GEN_PVAR_152 s f) (@lem4596890 A f)). Qed.
Lemma lem4596892 {A : Type'} (GEN_PVAR_152 : A -> Prop) (s : A -> Prop) : (term101 A GEN_PVAR_152 s) = (term102 A GEN_PVAR_152 s).
Proof. exact (fun_ext (fun f : A -> Prop => @lem4596891 A GEN_PVAR_152 s f)). Qed.
Lemma lem4596893 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4596894 {A : Type'} (GEN_PVAR_152 : A -> Prop) (s : A -> Prop) : (term103 A GEN_PVAR_152 s) = (term104 A GEN_PVAR_152 s).
Proof. exact (MK_COMB (@lem4596893 A) (@lem4596892 A GEN_PVAR_152 s)). Qed.
Lemma lem4596895 {A : Type'} (s : A -> Prop) : (term105 A s) = (term106 A s).
Proof. exact (fun_ext (fun GEN_PVAR_152 : A -> Prop => @lem4596894 A GEN_PVAR_152 s)). Qed.
Lemma lem4596896 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4596897 {A : Type'} (s : A -> Prop) : (term107 A s) = (term57 A s).
Proof. exact (MK_COMB (@lem4596896 A) (@lem4596895 A s)). Qed.
Lemma lem4596898 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x) = (@IN (A -> Prop) x).
Proof. exact (eq_refl (@IN (A -> Prop) x)). Qed.
Lemma lem4596899 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term93 A x s) = (term108 A x s).
Proof. exact (MK_COMB (@lem4596898 A x) (@lem4596897 A s)). Qed.
Lemma lem4596900 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4596901 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term109 A x s) = (term110 A x s).
Proof. exact (MK_COMB (@lem4596900) (@lem4596899 A x s)). Qed.
Lemma lem4596902 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term94 A s x) = (term96 A s x).
Proof. exact (eq_refl (term94 A s x)). Qed.
Lemma lem4596903 {A : Type'} (s : A -> Prop) (x : A -> Prop) : ((term93 A x s) = (term94 A s x)) = ((term108 A x s) = (term96 A s x)).
Proof. exact (MK_COMB (@lem4596901 A x s) (@lem4596902 A s x)). Qed.
Lemma lem4596904 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term108 A x s) = (term96 A s x).
Proof. exact (EQ_MP (@lem4596903 A s x) (@lem4596886 A s x)). Qed.
Lemma lem4596914 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem4596741 A P x) (@lem4596740 A P x)). Qed.
Lemma lem4596915 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4596914 A P x). Qed.
Lemma lem4596916 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4596915 A s x). Qed.
Lemma lem4596917 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4596918 {A : Type'} (s : A -> Prop) (x : A) : (term85 A x s) = (term86 A s x).
Proof. exact (MK_COMB (@lem4596917) (@lem4596916 A s x)). Qed.
Lemma lem4596920 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem4596752 A x) (@lem4596751 A x)). Qed.
Lemma lem4596921 (x : Prop) : (@IN Prop x (@UNIV Prop)) = True.
Proof. exact (@lem4596920 Prop x). Qed.
Lemma lem4596922 {A : Type'} (x : A -> Prop) (x' : A) : (term111 A x x') = True.
Proof. exact (@lem4596921 (x x')). Qed.
Lemma lem4596923 {A : Type'} (x : A -> Prop) (s : A -> Prop) (x' : A) : (term112 A s x x') = (term113 A s x').
Proof. exact (MK_COMB (@lem4596918 A s x') (@lem4596922 A x x')). Qed.
Lemma lem4596925 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4596926 {A : Type'} (s : A -> Prop) (x : A) : (term113 A s x) = True.
Proof. exact (@lem4596925 (s x)). Qed.
Lemma lem4596927 {A : Type'} (s : A -> Prop) (x : A -> Prop) (x' : A) : (term112 A s x x') = True.
Proof. exact (TRANS (@lem4596923 A x s x') (@lem4596926 A s x')). Qed.
Lemma lem4596928 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term114 A s x) = (term115 A).
Proof. exact (fun_ext (fun x' : A => @lem4596927 A s x x')). Qed.
Lemma lem4596929 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4596930 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term116 A s x) = (term117 A).
Proof. exact (MK_COMB (@lem4596929 A) (@lem4596928 A s x)). Qed.
Lemma lem4596932 {A : Type'} (t : Prop) : (term118 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4596933 {A : Type'} (t : Prop) : (term118 A t) = t.
Proof. exact (@lem4596932 A t). Qed.
Lemma lem4596934 {A : Type'} : (term117 A) = True.
Proof. exact (@lem4596933 A True). Qed.
Lemma lem4596935 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term116 A s x) = True.
Proof. exact (TRANS (@lem4596930 A s x) (@lem4596934 A)). Qed.
Lemma lem4596936 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4596937 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term119 A s x) = (and True).
Proof. exact (MK_COMB (@lem4596936) (@lem4596935 A s x)). Qed.
Lemma lem4596945 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem4596741 A P x) (@lem4596740 A P x)). Qed.
Lemma lem4596946 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4596945 A P x). Qed.
Lemma lem4596947 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4596946 A s x). Qed.
Lemma lem4596948 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4596949 {A : Type'} (s : A -> Prop) (x : A) : (term120 A x s) = (term121 A s x).
Proof. exact (MK_COMB (@lem4596948) (@lem4596947 A s x)). Qed.
Lemma lem4596950 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4596951 {A : Type'} (s : A -> Prop) (x : A) : (term122 A x s) = (term123 A s x).
Proof. exact (MK_COMB (@lem4596950) (@lem4596949 A s x)). Qed.
Lemma lem4596953 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4596954 {A : Type'} (x : A -> Prop) (x' : A) : ((x x') = False) = (term121 A x x').
Proof. exact (@lem4596953 (x x')). Qed.
Lemma lem4596955 {A : Type'} (s : A -> Prop) (x : A -> Prop) (x' : A) : (term124 A s x x') = (term125 A s x x').
Proof. exact (MK_COMB (@lem4596951 A s x') (@lem4596954 A x x')). Qed.
Lemma lem4596957 (t2 : Prop) (t1 : Prop) : (term43 t1 t2) = (t2 -> t1).
Proof. exact (EQ_MP (@lem4596735 t2 t1) (@lem4596734 t1 t2)). Qed.
Lemma lem4596958 {A : Type'} (x : A -> Prop) (s : A -> Prop) (x' : A) : (term125 A s x x') = (term88 A x s x').
Proof. exact (@lem4596957 (x x') (s x')). Qed.
Lemma lem4596961 {A : Type'} (x : A -> Prop) (s : A -> Prop) (x' : A) : (term124 A s x x') = (term88 A x s x').
Proof. exact (TRANS (@lem4596955 A s x x') (@lem4596958 A x s x')). Qed.
Lemma lem4596962 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term126 A s x) = (term90 A x s).
Proof. exact (fun_ext (fun x' : A => @lem4596961 A x s x')). Qed.
Lemma lem4596963 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4596964 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term127 A s x) = (term91 A x s).
Proof. exact (MK_COMB (@lem4596963 A) (@lem4596962 A x s)). Qed.
Lemma lem4596969 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term96 A s x) = (term128 A x s).
Proof. exact (MK_COMB (@lem4596937 A s x) (@lem4596964 A x s)). Qed.
Lemma lem4596971 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4596972 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term128 A x s) = (term91 A x s).
Proof. exact (@lem4596971 (term91 A x s)). Qed.
Lemma lem4596979 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term96 A s x) = (term91 A x s).
Proof. exact (TRANS (@lem4596969 A x s) (@lem4596972 A x s)). Qed.
Lemma lem4596980 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term108 A x s) = (term91 A x s).
Proof. exact (TRANS (@lem4596904 A s x) (@lem4596979 A x s)). Qed.
Lemma lem4596981 {A : Type'} (x : A -> Prop) (s : A -> Prop) : ((term82 A x s) = (term108 A x s)) = ((term91 A x s) = (term91 A x s)).
Proof. exact (MK_COMB (@lem4596882 A x s) (@lem4596980 A x s)). Qed.
Lemma lem4596983 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4596984 (x : Prop) : (x = x) = True.
Proof. exact (@lem4596983 Prop x). Qed.
Lemma lem4596985 {A : Type'} (x : A -> Prop) (s : A -> Prop) : ((term91 A x s) = (term91 A x s)) = True.
Proof. exact (@lem4596984 (term91 A x s)). Qed.
Lemma lem4596986 {A : Type'} (x : A -> Prop) (s : A -> Prop) : ((term82 A x s) = (term108 A x s)) = True.
Proof. exact (TRANS (@lem4596981 A x s) (@lem4596985 A x s)). Qed.
Lemma lem4596987 {A : Type'} (s : A -> Prop) : (term129 A s) = (term130 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4596986 A x s)). Qed.
Lemma lem4596988 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4596989 {A : Type'} (s : A -> Prop) : (term66 A s) = (term131 A).
Proof. exact (MK_COMB (@lem4596988 A) (@lem4596987 A s)). Qed.
Lemma lem4596991 {A : Type'} (t : Prop) : (term118 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4596992 {A : Type'} (t : Prop) : (term132 A t) = t.
Proof. exact (@lem4596991 (A -> Prop) t). Qed.
Lemma lem4596993 {A : Type'} : (term131 A) = True.
Proof. exact (@lem4596992 A True). Qed.
Lemma lem4596994 {A : Type'} (s : A -> Prop) : (term66 A s) = True.
Proof. exact (TRANS (@lem4596989 A s) (@lem4596993 A)). Qed.
Lemma lem4596995 {A : Type'} (s : A -> Prop) : ((term56 A s) = (term57 A s)) = True.
Proof. exact (TRANS (@lem4596818 A s) (@lem4596994 A s)). Qed.
Lemma lem4596996 {A : Type'} (s : A -> Prop) : True = ((term56 A s) = (term57 A s)).
Proof. exact (SYM (@lem4596995 A s)). Qed.
Lemma lem4596997 {A : Type'} (s : A -> Prop) : (term56 A s) = (term57 A s).
Proof. exact (EQ_MP (@lem4596996 A s) (@lem0)). Qed.
Lemma lem4596999 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (d : B) (n : nat) (m : nat) : term25 A B t s d n m.
Proof. exact (EQ_MP (@lem4596729 A B t s d n m) (@lem4596728 A B t s d n m)). Qed.
Lemma lem4597000 {A : Type'} (t : Prop -> Prop) (s : A -> Prop) (d : Prop) (n : nat) (m : nat) : term133 A t s d n m.
Proof. exact (@lem4596999 A Prop t s d n m). Qed.
Lemma lem4597001 {A : Type'} (s : A -> Prop) (n : nat) : term134 A s n.
Proof. exact (@lem4597000 A (@UNIV Prop) s False term135 n). Qed.
Lemma lem4597002 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = ((@HAS_SIZE A s n) = True).
Proof. exact (@lem7 (@HAS_SIZE A s n)). Qed.
Lemma lem4597007 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : (@HAS_SIZE A s n) = True.
Proof. exact (EQ_MP (@lem4597002 A s n) (@lem4596798 A s n h1)). Qed.
Lemma lem4597008 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4597009 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : (term136 A s n) = (and True).
Proof. exact (MK_COMB (@lem4597008) (@lem4597007 A s n h1)). Qed.
Lemma lem4597010 : term137 = term137.
Proof. exact (eq_refl term137). Qed.
Lemma lem4597011 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : (term138 A s n) = term139.
Proof. exact (MK_COMB (@lem4597009 A s n h1) (@lem4597010)). Qed.
Lemma lem4597013 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4597014 : term139 = term137.
Proof. exact (@lem4597013 term137). Qed.
Lemma lem4597015 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : (term138 A s n) = term137.
Proof. exact (TRANS (@lem4597011 A s n h1) (@lem4597014)). Qed.
Lemma lem4597016 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : term137 = (term138 A s n).
Proof. exact (SYM (@lem4597015 A s n h1)). Qed.
Lemma lem4597017 : term140 = term141.
Proof. exact (@lem912741). Qed.
Lemma lem4597018 : (term140 = term141) = (term142 = term135).
Proof. exact (@lem1005477 (BIT1 0) term141). Qed.
Lemma lem4597019 : term142 = term135.
Proof. exact (EQ_MP (@lem4597018) (@lem4597017)). Qed.
Lemma lem4597020 : term135 = term142.
Proof. exact (SYM (@lem4597019)). Qed.
Lemma lem4597021 : (@HAS_SIZE Prop (@UNIV Prop)) = (@HAS_SIZE Prop (@UNIV Prop)).
Proof. exact (eq_refl (@HAS_SIZE Prop (@UNIV Prop))). Qed.
Lemma lem4597022 : term137 = term143.
Proof. exact (MK_COMB (@lem4597021) (@lem4597020)). Qed.
Lemma lem4597024 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term144 _100499 s n) = (term145 _100499 n s).
Proof. exact (proj2 (@lem3887954 _100499 n s)). Qed.
Lemma lem4597025 (n : nat) (s : Prop -> Prop) : (term146 s n) = (term147 n s).
Proof. exact (@lem4597024 Prop n s). Qed.
Lemma lem4597026 : term143 = term148.
Proof. exact (@lem4597025 term149 (@UNIV Prop)). Qed.
Lemma lem4597027 : term137 = term148.
Proof. exact (TRANS (@lem4597022) (@lem4597026)). Qed.
Lemma lem4597028 : term150 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4597029 : (term150 = (BIT1 0)) = (term151 = term149).
Proof. exact (@lem1005477 0 (BIT1 0)). Qed.
Lemma lem4597030 : term151 = term149.
Proof. exact (EQ_MP (@lem4597029) (@lem4597028)). Qed.
Lemma lem4597031 : term149 = term151.
Proof. exact (SYM (@lem4597030)). Qed.
Lemma lem4597032 (t : Prop -> Prop) : (@HAS_SIZE Prop t) = (@HAS_SIZE Prop t).
Proof. exact (eq_refl (@HAS_SIZE Prop t)). Qed.
Lemma lem4597033 (t : Prop -> Prop) : (term152 t) = (term153 t).
Proof. exact (MK_COMB (@lem4597032 t) (@lem4597031)). Qed.
Lemma lem4597034 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4597035 (t : Prop -> Prop) : (term154 t) = (term155 t).
Proof. exact (MK_COMB (@lem4597034) (@lem4597033 t)). Qed.
Lemma lem4597036 (a : Prop) (t : Prop -> Prop) : (term156 a t) = (term156 a t).
Proof. exact (eq_refl (term156 a t)). Qed.
Lemma lem4597037 (a : Prop) (t : Prop -> Prop) : (term157 a t) = (term158 a t).
Proof. exact (MK_COMB (@lem4597035 t) (@lem4597036 a t)). Qed.
Lemma lem4597038 (a : Prop) : (term159 a) = (term160 a).
Proof. exact (fun_ext (fun t : Prop -> Prop => @lem4597037 a t)). Qed.
Lemma lem4597039 : (@ex (Prop -> Prop)) = (@ex (Prop -> Prop)).
Proof. exact (eq_refl (@ex (Prop -> Prop))). Qed.
Lemma lem4597040 (a : Prop) : (term161 a) = (term162 a).
Proof. exact (MK_COMB (@lem4597039) (@lem4597038 a)). Qed.
Lemma lem4597042 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term163 _100607 n P) = (term164 _100607 n P).
Proof. exact (proj2 (@lem3892933 _100607 n P)). Qed.
Lemma lem4597043 (n : nat) (P : type920) : (term165 n P) = (term166 n P).
Proof. exact (@lem4597042 Prop n P). Qed.
Lemma lem4597044 (a : Prop) : (term167 a) = (term168 a).
Proof. exact (@lem4597043 (NUMERAL 0) (term169 a)). Qed.
Lemma lem4597045 (a : Prop) (t : Prop -> Prop) : (term170 a t) = (term156 a t).
Proof. exact (eq_refl (term170 a t)). Qed.
Lemma lem4597046 (t : Prop -> Prop) : (term155 t) = (term155 t).
Proof. exact (eq_refl (term155 t)). Qed.
Lemma lem4597047 (a : Prop) (t : Prop -> Prop) : (term171 a t) = (term158 a t).
Proof. exact (MK_COMB (@lem4597046 t) (@lem4597045 a t)). Qed.
Lemma lem4597048 (a : Prop) : (term172 a) = (term160 a).
Proof. exact (fun_ext (fun t : Prop -> Prop => @lem4597047 a t)). Qed.
Lemma lem4597049 : (@ex (Prop -> Prop)) = (@ex (Prop -> Prop)).
Proof. exact (eq_refl (@ex (Prop -> Prop))). Qed.
Lemma lem4597050 (a : Prop) : (term167 a) = (term162 a).
Proof. exact (MK_COMB (@lem4597049) (@lem4597048 a)). Qed.
Lemma lem4597051 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4597052 (a : Prop) : (term173 a) = (term174 a).
Proof. exact (MK_COMB (@lem4597051) (@lem4597050 a)). Qed.
Lemma lem4597053 (a : Prop) (a' : Prop) (t : Prop -> Prop) : (term175 a a' t) = (term176 a a' t).
Proof. exact (eq_refl (term175 a a' t)). Qed.
Lemma lem4597054 (a' : Prop) (t : Prop -> Prop) : (term177 a' t) = (term177 a' t).
Proof. exact (eq_refl (term177 a' t)). Qed.
Lemma lem4597055 (a : Prop) (a' : Prop) (t : Prop -> Prop) : (term178 a a' t) = (term179 a a' t).
Proof. exact (MK_COMB (@lem4597054 a' t) (@lem4597053 a a' t)). Qed.
Lemma lem4597056 (t : Prop -> Prop) : (term180 t) = (term180 t).
Proof. exact (eq_refl (term180 t)). Qed.
Lemma lem4597057 (a : Prop) (a' : Prop) (t : Prop -> Prop) : (term181 a a' t) = (term182 a a' t).
Proof. exact (MK_COMB (@lem4597056 t) (@lem4597055 a a' t)). Qed.
Lemma lem4597058 (a : Prop) (a' : Prop) : (term183 a a') = (term184 a a').
Proof. exact (fun_ext (fun t : Prop -> Prop => @lem4597057 a a' t)). Qed.
Lemma lem4597059 : (@ex (Prop -> Prop)) = (@ex (Prop -> Prop)).
Proof. exact (eq_refl (@ex (Prop -> Prop))). Qed.
Lemma lem4597060 (a : Prop) (a' : Prop) : (term185 a a') = (term186 a a').
Proof. exact (MK_COMB (@lem4597059) (@lem4597058 a a')). Qed.
Lemma lem4597061 (a : Prop) : (term187 a) = (term188 a).
Proof. exact (fun_ext (fun a' : Prop => @lem4597060 a a')). Qed.
Lemma lem4597062 : (@ex Prop) = (@ex Prop).
Proof. exact (eq_refl (@ex Prop)). Qed.
Lemma lem4597063 (a : Prop) : (term168 a) = (term189 a).
Proof. exact (MK_COMB (@lem4597062) (@lem4597061 a)). Qed.
Lemma lem4597064 (a : Prop) : ((term167 a) = (term168 a)) = ((term162 a) = (term189 a)).
Proof. exact (MK_COMB (@lem4597052 a) (@lem4597063 a)). Qed.
Lemma lem4597065 (a : Prop) : (term162 a) = (term189 a).
Proof. exact (EQ_MP (@lem4597064 a) (@lem4597044 a)). Qed.
Lemma lem4597066 (a : Prop) : (term161 a) = (term189 a).
Proof. exact (TRANS (@lem4597040 a) (@lem4597065 a)). Qed.
Lemma lem4597068 {_100607 : Type'} (P : type686 _100607) : (term190 _100607 P) = (P (@EMPTY _100607)).
Proof. exact (proj1 (@lem3892933 _100607 (@el nat) P)). Qed.
Lemma lem4597069 (P : type920) : (term191 P) = (P (@EMPTY Prop)).
Proof. exact (@lem4597068 Prop P). Qed.
Lemma lem4597070 (a : Prop) (a' : Prop) : (term192 a a') = (term193 a a').
Proof. exact (@lem4597069 (term194 a a')). Qed.
Lemma lem4597071 (a : Prop) (a' : Prop) (t : Prop -> Prop) : (term195 a a' t) = (term179 a a' t).
Proof. exact (eq_refl (term195 a a' t)). Qed.
Lemma lem4597072 (t : Prop -> Prop) : (term180 t) = (term180 t).
Proof. exact (eq_refl (term180 t)). Qed.
Lemma lem4597073 (a : Prop) (a' : Prop) (t : Prop -> Prop) : (term196 a a' t) = (term182 a a' t).
Proof. exact (MK_COMB (@lem4597072 t) (@lem4597071 a a' t)). Qed.
Lemma lem4597074 (a : Prop) (a' : Prop) : (term197 a a') = (term184 a a').
Proof. exact (fun_ext (fun t : Prop -> Prop => @lem4597073 a a' t)). Qed.
Lemma lem4597075 : (@ex (Prop -> Prop)) = (@ex (Prop -> Prop)).
Proof. exact (eq_refl (@ex (Prop -> Prop))). Qed.
Lemma lem4597076 (a : Prop) (a' : Prop) : (term192 a a') = (term186 a a').
Proof. exact (MK_COMB (@lem4597075) (@lem4597074 a a')). Qed.
Lemma lem4597077 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4597078 (a : Prop) (a' : Prop) : (term198 a a') = (term199 a a').
Proof. exact (MK_COMB (@lem4597077) (@lem4597076 a a')). Qed.
Lemma lem4597079 (a : Prop) (a' : Prop) : (term193 a a') = (term200 a a').
Proof. exact (eq_refl (term193 a a')). Qed.
Lemma lem4597080 (a : Prop) (a' : Prop) : ((term192 a a') = (term193 a a')) = ((term186 a a') = (term200 a a')).
Proof. exact (MK_COMB (@lem4597078 a a') (@lem4597079 a a')). Qed.
Lemma lem4597081 (a : Prop) (a' : Prop) : (term186 a a') = (term200 a a').
Proof. exact (EQ_MP (@lem4597080 a a') (@lem4597070 a a')). Qed.
Lemma lem4597082 (a : Prop) : (term188 a) = (term201 a).
Proof. exact (fun_ext (fun a' : Prop => @lem4597081 a a')). Qed.
Lemma lem4597083 : (@ex Prop) = (@ex Prop).
Proof. exact (eq_refl (@ex Prop)). Qed.
Lemma lem4597084 (a : Prop) : (term189 a) = (term202 a).
Proof. exact (MK_COMB (@lem4597083) (@lem4597082 a)). Qed.
Lemma lem4597085 (a : Prop) : (term161 a) = (term202 a).
Proof. exact (TRANS (@lem4597066 a) (@lem4597084 a)). Qed.
Lemma lem4597086 : term203 = term204.
Proof. exact (fun_ext (fun a : Prop => @lem4597085 a)). Qed.
Lemma lem4597087 : (@ex Prop) = (@ex Prop).
Proof. exact (eq_refl (@ex Prop)). Qed.
Lemma lem4597088 : term148 = term205.
Proof. exact (MK_COMB (@lem4597087) (@lem4597086)). Qed.
Lemma lem4597089 : term137 = term205.
Proof. exact (TRANS (@lem4597027) (@lem4597088)). Qed.
Lemma lem4597091 {_100554 : Type'} (a : _100554) (P : Prop) : (term206 _100554 a P) = P.
Proof. exact (proj1 (@lem3888988 _100554 (@el _100554) a (@el (_100554 -> Prop)) P)). Qed.
Lemma lem4597092 (a : Prop) (P : Prop) : (term207 a P) = P.
Proof. exact (@lem4597091 Prop a P). Qed.
Lemma lem4597093 (a : Prop) (a' : Prop) : (term200 a a') = (term208 a a').
Proof. exact (@lem4597092 a' (term208 a a')). Qed.
Lemma lem4597095 {_100554 : Type'} (a : _100554) (b : _100554) (P : Prop) : (term209 _100554 a b P) = (term210 _100554 a b P).
Proof. exact (proj1 (@lem3892937 _100554 b a (@el (_100554 -> Prop)) P)). Qed.
Lemma lem4597096 (a : Prop) (b : Prop) (P : Prop) : (term211 a b P) = (term212 a b P).
Proof. exact (@lem4597095 Prop a b P). Qed.
Lemma lem4597101 (a : Prop) (a' : Prop) : (term208 a a') = (term213 a a').
Proof. exact (@lem4597096 a a' ((@UNIV Prop) = (term214 a a'))). Qed.
Lemma lem4597102 (a : Prop) (a' : Prop) : (term200 a a') = (term213 a a').
Proof. exact (TRANS (@lem4597093 a a') (@lem4597101 a a')). Qed.
Lemma lem4597103 (a : Prop) : (term201 a) = (term215 a).
Proof. exact (fun_ext (fun a' : Prop => @lem4597102 a a')). Qed.
Lemma lem4597104 : (@ex Prop) = (@ex Prop).
Proof. exact (eq_refl (@ex Prop)). Qed.
Lemma lem4597105 (a : Prop) : (term202 a) = (term216 a).
Proof. exact (MK_COMB (@lem4597104) (@lem4597103 a)). Qed.
Lemma lem4597106 : term204 = term217.
Proof. exact (fun_ext (fun a : Prop => @lem4597105 a)). Qed.
Lemma lem4597107 : (@ex Prop) = (@ex Prop).
Proof. exact (eq_refl (@ex Prop)). Qed.
Lemma lem4597108 : term205 = term218.
Proof. exact (MK_COMB (@lem4597107) (@lem4597106)). Qed.
Lemma lem4597109 : term137 = term218.
Proof. exact (TRANS (@lem4597089) (@lem4597108)). Qed.
Lemma lem4597110 : term218 = term137.
Proof. exact (SYM (@lem4597109)). Qed.
Lemma lem4597114 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem4597115 : (True = False) = False.
Proof. exact (@lem4597114 False). Qed.
Lemma lem4597116 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4597117 : term219 = (~ False).
Proof. exact (MK_COMB (@lem4597116) (@lem4597115)). Qed.
Lemma lem4597119 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4597120 : term219 = True.
Proof. exact (TRANS (@lem4597117) (@lem4597119)). Qed.
Lemma lem4597121 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4597122 : term220 = (and True).
Proof. exact (MK_COMB (@lem4597121) (@lem4597120)). Qed.
Lemma lem4597126 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term14 A s t).
Proof. exact (EQ_MP (@lem4596685 A s t) (@lem4596684 A s t)). Qed.
Lemma lem4597127 (s : Prop -> Prop) (t : Prop -> Prop) : (s = t) = (term221 s t).
Proof. exact (@lem4597126 Prop s t). Qed.
Lemma lem4597128 : ((@UNIV Prop) = term222) = term223.
Proof. exact (@lem4597127 (@UNIV Prop) term222). Qed.
Lemma lem4597138 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem4596679 A x) (@lem4596678 A x)). Qed.
Lemma lem4597139 (x : Prop) : (@IN Prop x (@UNIV Prop)) = True.
Proof. exact (@lem4597138 Prop x). Qed.
Lemma lem4597140 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4597141 (x : Prop) : (term224 x) = (@eq Prop True).
Proof. exact (MK_COMB (@lem4597140) (@lem4597139 x)). Qed.
Lemma lem4597143 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem4596674 A y x s) (@lem4596673 A y x s)). Qed.
Lemma lem4597144 (y : Prop) (x : Prop) (s : Prop -> Prop) : (term225 x y s) = (term226 y x s).
Proof. exact (@lem4597143 Prop y x s). Qed.
Lemma lem4597145 (x : Prop) : (term227 x) = (term228 x).
Proof. exact (@lem4597144 True x (@INSERT Prop False (@EMPTY Prop))). Qed.
Lemma lem4597149 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem4597150 (x : Prop) : (x = True) = x.
Proof. exact (@lem4597149 x). Qed.
Lemma lem4597151 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4597152 (x : Prop) : (term229 x) = (or x).
Proof. exact (MK_COMB (@lem4597151) (@lem4597150 x)). Qed.
Lemma lem4597154 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem4596674 A y x s) (@lem4596673 A y x s)). Qed.
Lemma lem4597155 (y : Prop) (x : Prop) (s : Prop -> Prop) : (term225 x y s) = (term226 y x s).
Proof. exact (@lem4597154 Prop y x s). Qed.
Lemma lem4597156 (x : Prop) : (term230 x) = (term231 x).
Proof. exact (@lem4597155 False x (@EMPTY Prop)). Qed.
Lemma lem4597160 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4597161 (x : Prop) : (x = False) = (~ x).
Proof. exact (@lem4597160 x). Qed.
Lemma lem4597162 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4597163 (x : Prop) : (term232 x) = (term233 x).
Proof. exact (MK_COMB (@lem4597162) (@lem4597161 x)). Qed.
Lemma lem4597165 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4596665 A x (@lem4596664 A x)). Qed.
Lemma lem4597166 (x : Prop) : (@IN Prop x (@EMPTY Prop)) = False.
Proof. exact (@lem4597165 Prop x). Qed.
Lemma lem4597167 (x : Prop) : (term231 x) = (term234 x).
Proof. exact (MK_COMB (@lem4597163 x) (@lem4597166 x)). Qed.
Lemma lem4597169 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem4597170 (x : Prop) : (term234 x) = (~ x).
Proof. exact (@lem4597169 (~ x)). Qed.
Lemma lem4597171 (x : Prop) : (term231 x) = (~ x).
Proof. exact (TRANS (@lem4597167 x) (@lem4597170 x)). Qed.
Lemma lem4597172 (x : Prop) : (term230 x) = (~ x).
Proof. exact (TRANS (@lem4597156 x) (@lem4597171 x)). Qed.
Lemma lem4597173 (x : Prop) : (term228 x) = (term235 x).
Proof. exact (MK_COMB (@lem4597152 x) (@lem4597172 x)). Qed.
Lemma lem4597176 (x : Prop) : (term227 x) = (term235 x).
Proof. exact (TRANS (@lem4597145 x) (@lem4597173 x)). Qed.
Lemma lem4597177 (x : Prop) : ((@IN Prop x (@UNIV Prop)) = (term227 x)) = (True = (term235 x)).
Proof. exact (MK_COMB (@lem4597141 x) (@lem4597176 x)). Qed.
Lemma lem4597179 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem4597180 (x : Prop) : (True = (term235 x)) = (term235 x).
Proof. exact (@lem4597179 (term235 x)). Qed.
Lemma lem4597183 (x : Prop) : ((@IN Prop x (@UNIV Prop)) = (term227 x)) = (term235 x).
Proof. exact (TRANS (@lem4597177 x) (@lem4597180 x)). Qed.
Lemma lem4597184 : term236 = term237.
Proof. exact (fun_ext (fun x : Prop => @lem4597183 x)). Qed.
Lemma lem4597185 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem4597186 : term223 = term238.
Proof. exact (MK_COMB (@lem4597185) (@lem4597184)). Qed.
Lemma lem4597191 : ((@UNIV Prop) = term222) = term238.
Proof. exact (TRANS (@lem4597128) (@lem4597186)). Qed.
Lemma lem4597192 : term239 = term240.
Proof. exact (MK_COMB (@lem4597122) (@lem4597191)). Qed.
Lemma lem4597194 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4597195 : term240 = term238.
Proof. exact (@lem4597194 term238). Qed.
Lemma lem4597202 : term239 = term238.
Proof. exact (TRANS (@lem4597192) (@lem4597195)). Qed.
Lemma lem4597203 : term238 = term239.
Proof. exact (SYM (@lem4597202)). Qed.
Lemma lem4597208 (x : Prop) : term241 x.
Proof. exact (@lem9851 x). Qed.
Lemma lem4597209 (x : Prop) : (term241 x) = (term242 x).
Proof. exact (eq_refl (term241 x)). Qed.
Lemma lem4597210 (x : Prop) : term242 x.
Proof. exact (EQ_MP (@lem4597209 x) (@lem4597208 x)). Qed.
Lemma lem4597211 (x : Prop) (h1 : x = True) : x = True.
Proof. exact (h1). Qed.
Lemma lem4597212 (x : Prop) (h1 : x = False) : x = False.
Proof. exact (h1). Qed.
Lemma lem4597217 : term237 = term237.
Proof. exact (eq_refl term237). Qed.
Lemma lem4597218 (x : Prop) (h1 : x = True) : (term243 x) = term244.
Proof. exact (MK_COMB (@lem4597217) (@lem4597211 x h1)). Qed.
Lemma lem4597219 : term244 = term245.
Proof. exact (eq_refl term244). Qed.
Lemma lem4597220 (x : Prop) : (term246 x) = (term246 x).
Proof. exact (eq_refl (term246 x)). Qed.
Lemma lem4597221 (x : Prop) : ((term243 x) = term244) = ((term243 x) = term245).
Proof. exact (MK_COMB (@lem4597220 x) (@lem4597219)). Qed.
Lemma lem4597222 (x : Prop) : (term243 x) = (term235 x).
Proof. exact (eq_refl (term243 x)). Qed.
Lemma lem4597223 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4597224 (x : Prop) : (term246 x) = (term247 x).
Proof. exact (MK_COMB (@lem4597223) (@lem4597222 x)). Qed.
Lemma lem4597225 : term245 = term245.
Proof. exact (eq_refl term245). Qed.
Lemma lem4597226 (x : Prop) : ((term243 x) = term245) = ((term235 x) = term245).
Proof. exact (MK_COMB (@lem4597224 x) (@lem4597225)). Qed.
Lemma lem4597227 (x : Prop) : ((term243 x) = term244) = ((term235 x) = term245).
Proof. exact (TRANS (@lem4597221 x) (@lem4597226 x)). Qed.
Lemma lem4597228 (x : Prop) (h1 : x = True) : (term235 x) = term245.
Proof. exact (EQ_MP (@lem4597227 x) (@lem4597218 x h1)). Qed.
Lemma lem4597229 (x : Prop) (h1 : x = True) : term245 = (term235 x).
Proof. exact (SYM (@lem4597228 x h1)). Qed.
Lemma lem4597230 : term237 = term237.
Proof. exact (eq_refl term237). Qed.
Lemma lem4597231 (x : Prop) (h1 : x = False) : (term243 x) = term248.
Proof. exact (MK_COMB (@lem4597230) (@lem4597212 x h1)). Qed.
Lemma lem4597232 : term248 = term249.
Proof. exact (eq_refl term248). Qed.
Lemma lem4597233 (x : Prop) : (term246 x) = (term246 x).
Proof. exact (eq_refl (term246 x)). Qed.
Lemma lem4597234 (x : Prop) : ((term243 x) = term248) = ((term243 x) = term249).
Proof. exact (MK_COMB (@lem4597233 x) (@lem4597232)). Qed.
Lemma lem4597235 (x : Prop) : (term243 x) = (term235 x).
Proof. exact (eq_refl (term243 x)). Qed.
Lemma lem4597236 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4597237 (x : Prop) : (term246 x) = (term247 x).
Proof. exact (MK_COMB (@lem4597236) (@lem4597235 x)). Qed.
Lemma lem4597238 : term249 = term249.
Proof. exact (eq_refl term249). Qed.
Lemma lem4597239 (x : Prop) : ((term243 x) = term249) = ((term235 x) = term249).
Proof. exact (MK_COMB (@lem4597237 x) (@lem4597238)). Qed.
Lemma lem4597240 (x : Prop) : ((term243 x) = term248) = ((term235 x) = term249).
Proof. exact (TRANS (@lem4597234 x) (@lem4597239 x)). Qed.
Lemma lem4597241 (x : Prop) (h1 : x = False) : (term235 x) = term249.
Proof. exact (EQ_MP (@lem4597240 x) (@lem4597231 x h1)). Qed.
Lemma lem4597242 (x : Prop) (h1 : x = False) : term249 = (term235 x).
Proof. exact (SYM (@lem4597241 x h1)). Qed.
Lemma lem4597244 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem4597245 : term245 = True.
Proof. exact (@lem4597244 (~ True)). Qed.
Lemma lem4597246 : True = term245.
Proof. exact (SYM (@lem4597245)). Qed.
Lemma lem4597247 : term245.
Proof. exact (EQ_MP (@lem4597246) (@lem0)). Qed.
Lemma lem4597249 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem4597250 : term249 = (~ False).
Proof. exact (@lem4597249 (~ False)). Qed.
Lemma lem4597252 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4597253 : term249 = True.
Proof. exact (TRANS (@lem4597250) (@lem4597252)). Qed.
Lemma lem4597254 : True = term249.
Proof. exact (SYM (@lem4597253)). Qed.
Lemma lem4597255 : term249.
Proof. exact (EQ_MP (@lem4597254) (@lem0)). Qed.
Lemma lem4597256 (x : Prop) (h1 : x = False) : term235 x.
Proof. exact (EQ_MP (@lem4597242 x h1) (@lem4597255)). Qed.
Lemma lem4597257 (x : Prop) (h1 : x = True) : term235 x.
Proof. exact (EQ_MP (@lem4597229 x h1) (@lem4597247)). Qed.
Lemma lem4597260 (x : Prop) : term235 x.
Proof. exact (or_elim (@lem4597210 x) (fun h0 : x = True => @lem4597257 x h0) (fun h0 : x = False => @lem4597256 x h0)). Qed.
Lemma lem4597265 : term238.
Proof. exact (fun x : Prop => @lem4597260 x). Qed.
Lemma lem4597266 : term239.
Proof. exact (EQ_MP (@lem4597203) (@lem4597265)). Qed.
Lemma lem4597267 : term250.
Proof. exact (ex_intro term251 False (@lem4597266)). Qed.
Lemma lem4597268 : term218.
Proof. exact (ex_intro term217 True (@lem4597267)). Qed.
Lemma lem4597269 : term137.
Proof. exact (EQ_MP (@lem4597110) (@lem4597268)). Qed.
Lemma lem4597270 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : term138 A s n.
Proof. exact (EQ_MP (@lem4597016 A s n h1) (@lem4597269)). Qed.
Lemma lem4597271 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : term61 A s n.
Proof. exact (@lem4597001 A s n (@lem4597270 A s n h1)). Qed.
Lemma lem4597272 {A : Type'} (s : A -> Prop) (n : nat) (h1 : (term56 A s) = (term57 A s)) (h2 : @HAS_SIZE A s n) : term63 A s n.
Proof. exact (EQ_MP (@lem4596812 A n s h1) (@lem4597271 A s n h2)). Qed.
Lemma lem4597273 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : ((term56 A s) = (term57 A s)) = (term63 A s n).
Proof. exact (prop_ext (fun h2 : (term56 A s) = (term57 A s) => @lem4597272 A s n h2 h1) (fun h2 : term63 A s n => @lem4596997 A s)). Qed.
Lemma lem4597274 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : term63 A s n.
Proof. exact (EQ_MP (@lem4597273 A s n h1) (@lem4596997 A s)). Qed.
Lemma lem4597275 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : (@HAS_SIZE A s n) = (term63 A s n).
Proof. exact (prop_ext (fun h2 : @HAS_SIZE A s n => @lem4597274 A s n h1) (fun h2 : term63 A s n => @lem4596798 A s n h1)). Qed.
Lemma lem4597276 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @HAS_SIZE A s n) : term63 A s n.
Proof. exact (EQ_MP (@lem4597275 A s n h1) (@lem4596798 A s n h1)). Qed.
Lemma lem4597277 {A : Type'} (s : A -> Prop) (n : nat) : term252 A s n.
Proof. exact (fun h0 : @HAS_SIZE A s n => @lem4597276 A s n h0). Qed.
Lemma lem4597282 {A : Type'} (s : A -> Prop) : term253 A s.
Proof. exact (fun n : nat => @lem4597277 A s n). Qed.
Lemma lem4597289 {A : Type'} : term254 A.
Proof. exact (fun s : A -> Prop => @lem4597282 A s). Qed.
