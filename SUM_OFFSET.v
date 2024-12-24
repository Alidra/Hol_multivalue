Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_OFFSET_term_abbrevs.
Require Import EQ_ADD_RCANCEL_spec.
Require Import NUMSEG_OFFSET_IMAGE_spec.
Require Import SUM_IMAGE_spec.
Require Import o_DEF_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Lemma lem7222771 {A B C : Type'} (f : B -> C) : term0 A B C f.
Proof. exact (@lem15397 A B C f). Qed.
Lemma lem7222772 {A B C : Type'} (f : B -> C) : (term0 A B C f) = (term1 A B C f).
Proof. exact (eq_refl (term0 A B C f)). Qed.
Lemma lem7222773 {A B C : Type'} (f : B -> C) : term1 A B C f.
Proof. exact (EQ_MP (@lem7222772 A B C f) (@lem7222771 A B C f)). Qed.
Lemma lem7222774 {A B C : Type'} (f : B -> C) (g : A -> B) : term2 A B C f g.
Proof. exact (@lem7222773 A B C f g). Qed.
Lemma lem7222775 {A B C : Type'} (f : B -> C) (g : A -> B) : (term2 A B C f g) = ((@o A B C f g) = (term3 A B C f g)).
Proof. exact (eq_refl (term2 A B C f g)). Qed.
Lemma lem7222785 (m : nat) : term4 m.
Proof. exact (@lem79714 m). Qed.
Lemma lem7222786 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem7222787 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem7222786 m) (@lem7222785 m)). Qed.
Lemma lem7222788 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem7222787 m n). Qed.
Lemma lem7222789 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem7222790 (m : nat) (n : nat) : term7 m n.
Proof. exact (EQ_MP (@lem7222789 m n) (@lem7222788 m n)). Qed.
Lemma lem7222791 (m : nat) (n : nat) (p : nat) : term8 m n p.
Proof. exact (@lem7222790 m n p). Qed.
Lemma lem7222792 (p : nat) (m : nat) (n : nat) : (term8 m n p) = (((Nat.add m p) = (Nat.add n p)) = (m = n)).
Proof. exact (eq_refl (term8 m n p)). Qed.
Lemma lem7222794 {_133152 _133176 : Type'} (f : _133176 -> _133152) : term9 _133152 _133176 f.
Proof. exact (@lem7124521 _133152 _133176 f). Qed.
Lemma lem7222795 {_133152 _133176 : Type'} (f : _133176 -> _133152) : (term9 _133152 _133176 f) = (term10 _133152 _133176 f).
Proof. exact (eq_refl (term9 _133152 _133176 f)). Qed.
Lemma lem7222796 {_133152 _133176 : Type'} (f : _133176 -> _133152) : term10 _133152 _133176 f.
Proof. exact (EQ_MP (@lem7222795 _133152 _133176 f) (@lem7222794 _133152 _133176 f)). Qed.
Lemma lem7222797 {_133152 _133176 : Type'} (f : _133176 -> _133152) (g : _133152 -> real) : term11 _133152 _133176 f g.
Proof. exact (@lem7222796 _133152 _133176 f g). Qed.
Lemma lem7222798 {_133152 _133176 : Type'} (g : _133152 -> real) (f : _133176 -> _133152) : (term11 _133152 _133176 f g) = (term12 _133152 _133176 g f).
Proof. exact (eq_refl (term11 _133152 _133176 f g)). Qed.
Lemma lem7222799 {_133152 _133176 : Type'} (g : _133152 -> real) (f : _133176 -> _133152) : term12 _133152 _133176 g f.
Proof. exact (EQ_MP (@lem7222798 _133152 _133176 g f) (@lem7222797 _133152 _133176 f g)). Qed.
Lemma lem7222800 {_133152 _133176 : Type'} (g : _133152 -> real) (f : _133176 -> _133152) (s : _133176 -> Prop) : term13 _133152 _133176 g f s.
Proof. exact (@lem7222799 _133152 _133176 g f s). Qed.
Lemma lem7222801 {_133152 _133176 : Type'} (s : _133176 -> Prop) (g : _133152 -> real) (f : _133176 -> _133152) : (term13 _133152 _133176 g f s) = (term14 _133152 _133176 s g f).
Proof. exact (eq_refl (term13 _133152 _133176 g f s)). Qed.
Lemma lem7222802 {_133152 _133176 : Type'} (s : _133176 -> Prop) (g : _133152 -> real) (f : _133176 -> _133152) : term14 _133152 _133176 s g f.
Proof. exact (EQ_MP (@lem7222801 _133152 _133176 s g f) (@lem7222800 _133152 _133176 g f s)). Qed.
Lemma lem7222803 {_133152 _133176 : Type'} (s : _133176 -> Prop) (f : _133176 -> _133152) (h1 : term15 _133152 _133176 s f) : term15 _133152 _133176 s f.
Proof. exact (h1). Qed.
Lemma lem7222804 {_133152 _133176 : Type'} (g : _133152 -> real) (s : _133176 -> Prop) (f : _133176 -> _133152) (h1 : term15 _133152 _133176 s f) : (term16 _133152 _133176 f s g) = (term17 _133152 _133176 s g f).
Proof. exact (@lem7222802 _133152 _133176 s g f (@lem7222803 _133152 _133176 s f h1)). Qed.
Lemma lem7222810 (m : nat) : term18 m.
Proof. exact (@lem5470571 m). Qed.
Lemma lem7222811 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem7222812 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem7222811 m) (@lem7222810 m)). Qed.
Lemma lem7222813 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem7222812 m n). Qed.
Lemma lem7222814 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem7222815 (m : nat) (n : nat) : term21 m n.
Proof. exact (EQ_MP (@lem7222814 m n) (@lem7222813 m n)). Qed.
Lemma lem7222816 (m : nat) (n : nat) (p : nat) : term22 m n p.
Proof. exact (@lem7222815 m n p). Qed.
Lemma lem7222817 (p : nat) (m : nat) (n : nat) : (term22 m n p) = ((term23 m n p) = (term24 p m n)).
Proof. exact (eq_refl (term22 m n p)). Qed.
Lemma lem7222838 (p : nat) (m : nat) (n : nat) : (term23 m n p) = (term24 p m n).
Proof. exact (EQ_MP (@lem7222817 p m n) (@lem7222816 m n p)). Qed.
Lemma lem7222839 : (@sum nat) = (@sum nat).
Proof. exact (eq_refl (@sum nat)). Qed.
Lemma lem7222840 (p : nat) (m : nat) (n : nat) : (term25 m n p) = (term26 p m n).
Proof. exact (MK_COMB (@lem7222839) (@lem7222838 p m n)). Qed.
Lemma lem7222841 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7222842 (p : nat) (m : nat) (n : nat) (f : nat -> real) : (term27 m n p f) = (term28 p m n f).
Proof. exact (MK_COMB (@lem7222840 p m n) (@lem7222841 f)). Qed.
Lemma lem7222844 {_133152 _133176 : Type'} (s : _133176 -> Prop) (g : _133152 -> real) (f : _133176 -> _133152) : term14 _133152 _133176 s g f.
Proof. exact (fun h0 : term15 _133152 _133176 s f => @lem7222804 _133152 _133176 g s f h0). Qed.
Lemma lem7222845 (s : nat -> Prop) (g : nat -> real) (f : nat -> nat) : term29 s g f.
Proof. exact (@lem7222844 nat nat s g f). Qed.
Lemma lem7222846 (m : nat) (n : nat) (f : nat -> real) (p : nat) : term30 m n f p.
Proof. exact (@lem7222845 (dotdot m n) f (term31 p)). Qed.
Lemma lem7222858 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term32 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7222859 (p : Prop) (q : Prop) (p' : Prop) : term33 p q p'.
Proof. exact (fun q' : Prop => @lem7222858 p q p' q'). Qed.
Lemma lem7222860 (p : Prop) (q : Prop) : term34 p q.
Proof. exact (fun p' : Prop => @lem7222859 p q p'). Qed.
Lemma lem7222861 (m : nat) (n : nat) (p : nat) (x : nat) (y : nat) : term35 m n p x y.
Proof. exact (@lem7222860 (term36 m n x p y) (x = y)). Qed.
Lemma lem7222862 (m : nat) (n : nat) (p : nat) (x : nat) (y : nat) (p' : Prop) : term37 m n p x y p'.
Proof. exact (@lem7222861 m n p x y p'). Qed.
Lemma lem7222863 (m : nat) (n : nat) (p : nat) (x : nat) (y : nat) (p' : Prop) : (term37 m n p x y p') = (term38 m n p x y p').
Proof. exact (eq_refl (term37 m n p x y p')). Qed.
Lemma lem7222864 (m : nat) (n : nat) (p : nat) (x : nat) (y : nat) (p' : Prop) : term38 m n p x y p'.
Proof. exact (EQ_MP (@lem7222863 m n p x y p') (@lem7222862 m n p x y p')). Qed.
Lemma lem7222865 (m : nat) (n : nat) (p : nat) (x : nat) (y : nat) (p' : Prop) (q' : Prop) : term39 m n p x y p' q'.
Proof. exact (@lem7222864 m n p x y p' q'). Qed.
Lemma lem7222866 (m : nat) (n : nat) (p : nat) (x : nat) (y : nat) (p' : Prop) (q' : Prop) : (term39 m n p x y p' q') = (term40 m n p x y p' q').
Proof. exact (eq_refl (term39 m n p x y p' q')). Qed.
Lemma lem7222867 (m : nat) (n : nat) (p : nat) (x : nat) (y : nat) (p' : Prop) (q' : Prop) : term40 m n p x y p' q'.
Proof. exact (EQ_MP (@lem7222866 m n p x y p' q') (@lem7222865 m n p x y p' q')). Qed.
Lemma lem7222875 {A B : Type'} (f : A -> B) (y : A) : (term41 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7222876 (f : nat -> nat) (y : nat) : (term42 f y) = (f y).
Proof. exact (@lem7222875 nat nat f y). Qed.
Lemma lem7222877 (p : nat) (x : nat) : (term43 p x) = (term44 p x).
Proof. exact (@lem7222876 (term31 p) x). Qed.
Lemma lem7222878 (i : nat) (p : nat) : (term44 p i) = (Nat.add i p).
Proof. exact (eq_refl (term44 p i)). Qed.
Lemma lem7222879 (p : nat) : (term45 p) = (term31 p).
Proof. exact (fun_ext (fun i : nat => @lem7222878 i p)). Qed.
Lemma lem7222880 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7222881 (p : nat) (x : nat) : (term43 p x) = (term44 p x).
Proof. exact (MK_COMB (@lem7222879 p) (@lem7222880 x)). Qed.
Lemma lem7222882 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7222883 (p : nat) (x : nat) : (term46 p x) = (term47 p x).
Proof. exact (MK_COMB (@lem7222882) (@lem7222881 p x)). Qed.
Lemma lem7222884 (x : nat) (p : nat) : (term44 p x) = (Nat.add x p).
Proof. exact (eq_refl (term44 p x)). Qed.
Lemma lem7222885 (x : nat) (p : nat) : ((term43 p x) = (term44 p x)) = ((term44 p x) = (Nat.add x p)).
Proof. exact (MK_COMB (@lem7222883 p x) (@lem7222884 x p)). Qed.
Lemma lem7222886 (x : nat) (p : nat) : (term44 p x) = (Nat.add x p).
Proof. exact (EQ_MP (@lem7222885 x p) (@lem7222877 p x)). Qed.
Lemma lem7222887 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7222888 (x : nat) (p : nat) : (term47 p x) = (term48 x p).
Proof. exact (MK_COMB (@lem7222887) (@lem7222886 x p)). Qed.
Lemma lem7222890 {A B : Type'} (f : A -> B) (y : A) : (term41 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7222891 (f : nat -> nat) (y : nat) : (term42 f y) = (f y).
Proof. exact (@lem7222890 nat nat f y). Qed.
Lemma lem7222892 (p : nat) (y : nat) : (term43 p y) = (term44 p y).
Proof. exact (@lem7222891 (term31 p) y). Qed.
Lemma lem7222893 (i : nat) (p : nat) : (term44 p i) = (Nat.add i p).
Proof. exact (eq_refl (term44 p i)). Qed.
Lemma lem7222894 (p : nat) : (term45 p) = (term31 p).
Proof. exact (fun_ext (fun i : nat => @lem7222893 i p)). Qed.
Lemma lem7222895 (y : nat) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7222896 (p : nat) (y : nat) : (term43 p y) = (term44 p y).
Proof. exact (MK_COMB (@lem7222894 p) (@lem7222895 y)). Qed.
Lemma lem7222897 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7222898 (p : nat) (y : nat) : (term46 p y) = (term47 p y).
Proof. exact (MK_COMB (@lem7222897) (@lem7222896 p y)). Qed.
Lemma lem7222899 (y : nat) (p : nat) : (term44 p y) = (Nat.add y p).
Proof. exact (eq_refl (term44 p y)). Qed.
Lemma lem7222900 (y : nat) (p : nat) : ((term43 p y) = (term44 p y)) = ((term44 p y) = (Nat.add y p)).
Proof. exact (MK_COMB (@lem7222898 p y) (@lem7222899 y p)). Qed.
Lemma lem7222901 (y : nat) (p : nat) : (term44 p y) = (Nat.add y p).
Proof. exact (EQ_MP (@lem7222900 y p) (@lem7222892 p y)). Qed.
Lemma lem7222902 (x : nat) (y : nat) (p : nat) : ((term44 p x) = (term44 p y)) = ((Nat.add x p) = (Nat.add y p)).
Proof. exact (MK_COMB (@lem7222888 x p) (@lem7222901 y p)). Qed.
Lemma lem7222904 (p : nat) (m : nat) (n : nat) : ((Nat.add m p) = (Nat.add n p)) = (m = n).
Proof. exact (EQ_MP (@lem7222792 p m n) (@lem7222791 m n p)). Qed.
Lemma lem7222905 (p : nat) (x : nat) (y : nat) : ((Nat.add x p) = (Nat.add y p)) = (x = y).
Proof. exact (@lem7222904 p x y). Qed.
Lemma lem7222908 (p : nat) (x : nat) (y : nat) : ((term44 p x) = (term44 p y)) = (x = y).
Proof. exact (TRANS (@lem7222902 x y p) (@lem7222905 p x y)). Qed.
Lemma lem7222909 (y : nat) (m : nat) (n : nat) : (term49 y m n) = (term49 y m n).
Proof. exact (eq_refl (term49 y m n)). Qed.
Lemma lem7222910 (p : nat) (m : nat) (n : nat) (x : nat) (y : nat) : (term50 m n x p y) = (term51 m n x y).
Proof. exact (MK_COMB (@lem7222909 y m n) (@lem7222908 p x y)). Qed.
Lemma lem7222915 (x : nat) (m : nat) (n : nat) : (term49 x m n) = (term49 x m n).
Proof. exact (eq_refl (term49 x m n)). Qed.
Lemma lem7222916 (p : nat) (m : nat) (n : nat) (x : nat) (y : nat) : (term36 m n x p y) = (term52 m n x y).
Proof. exact (MK_COMB (@lem7222915 x m n) (@lem7222910 p m n x y)). Qed.
Lemma lem7222923 (p : nat) (m : nat) (n : nat) (x : nat) (y : nat) (q' : Prop) : term53 p m n x y q'.
Proof. exact (@lem7222867 m n p x y (term52 m n x y) q'). Qed.
Lemma lem7222924 (p : nat) (m : nat) (n : nat) (x : nat) (y : nat) (q' : Prop) : term54 p m n x y q'.
Proof. exact (@lem7222923 p m n x y q' (@lem7222916 p m n x y)). Qed.
Lemma lem7222925 (m : nat) (n : nat) (x : nat) (y : nat) (h1 : term52 m n x y) : term52 m n x y.
Proof. exact (h1). Qed.
Lemma lem7222926 (m : nat) (n : nat) (x : nat) (y : nat) (h1 : term52 m n x y) : term51 m n x y.
Proof. exact (proj2 (@lem7222925 m n x y h1)). Qed.
Lemma lem7222937 (m : nat) (n : nat) (x : nat) (y : nat) (h1 : term52 m n x y) : x = y.
Proof. exact (proj2 (@lem7222926 m n x y h1)). Qed.
Lemma lem7222938 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7222939 (m : nat) (n : nat) (x : nat) (y : nat) (h1 : term52 m n x y) : (@eq nat x) = (@eq nat y).
Proof. exact (MK_COMB (@lem7222938) (@lem7222937 m n x y h1)). Qed.
Lemma lem7222940 (y : nat) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7222941 (m : nat) (n : nat) (x : nat) (y : nat) (h1 : term52 m n x y) : (x = y) = (y = y).
Proof. exact (MK_COMB (@lem7222939 m n x y h1) (@lem7222940 y)). Qed.
Lemma lem7222943 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7222944 (x : nat) : (x = x) = True.
Proof. exact (@lem7222943 nat x). Qed.
Lemma lem7222945 (y : nat) : (y = y) = True.
Proof. exact (@lem7222944 y). Qed.
Lemma lem7222946 (m : nat) (n : nat) (x : nat) (y : nat) (h1 : term52 m n x y) : (x = y) = True.
Proof. exact (TRANS (@lem7222941 m n x y h1) (@lem7222945 y)). Qed.
Lemma lem7222947 (m : nat) (n : nat) (x : nat) (y : nat) : term55 m n x y.
Proof. exact (fun h0 : term52 m n x y => @lem7222946 m n x y h0). Qed.
Lemma lem7222948 (p : nat) (m : nat) (n : nat) (x : nat) (y : nat) : term56 p m n x y.
Proof. exact (@lem7222924 p m n x y True). Qed.
Lemma lem7222949 (p : nat) (m : nat) (n : nat) (x : nat) (y : nat) : (term57 m n p x y) = (term58 m n x y).
Proof. exact (@lem7222948 p m n x y (@lem7222947 m n x y)). Qed.
Lemma lem7222951 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7222952 (m : nat) (n : nat) (x : nat) (y : nat) : (term58 m n x y) = True.
Proof. exact (@lem7222951 (term52 m n x y)). Qed.
Lemma lem7222953 (m : nat) (n : nat) (p : nat) (x : nat) (y : nat) : (term57 m n p x y) = True.
Proof. exact (TRANS (@lem7222949 p m n x y) (@lem7222952 m n x y)). Qed.
Lemma lem7222954 (m : nat) (n : nat) (p : nat) (x : nat) : (term59 m n p x) = term60.
Proof. exact (fun_ext (fun y : nat => @lem7222953 m n p x y)). Qed.
Lemma lem7222955 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7222956 (m : nat) (n : nat) (p : nat) (x : nat) : (term61 m n p x) = term62.
Proof. exact (MK_COMB (@lem7222955) (@lem7222954 m n p x)). Qed.
Lemma lem7222958 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7222959 (t : Prop) : (term64 t) = t.
Proof. exact (@lem7222958 nat t). Qed.
Lemma lem7222960 : term62 = True.
Proof. exact (@lem7222959 True). Qed.
Lemma lem7222961 (m : nat) (n : nat) (p : nat) (x : nat) : (term61 m n p x) = True.
Proof. exact (TRANS (@lem7222956 m n p x) (@lem7222960)). Qed.
Lemma lem7222962 (m : nat) (n : nat) (p : nat) : (term65 m n p) = term60.
Proof. exact (fun_ext (fun x : nat => @lem7222961 m n p x)). Qed.
Lemma lem7222963 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7222964 (m : nat) (n : nat) (p : nat) : (term66 m n p) = term62.
Proof. exact (MK_COMB (@lem7222963) (@lem7222962 m n p)). Qed.
Lemma lem7222966 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7222967 (t : Prop) : (term64 t) = t.
Proof. exact (@lem7222966 nat t). Qed.
Lemma lem7222968 : term62 = True.
Proof. exact (@lem7222967 True). Qed.
Lemma lem7222969 (m : nat) (n : nat) (p : nat) : (term66 m n p) = True.
Proof. exact (TRANS (@lem7222964 m n p) (@lem7222968)). Qed.
Lemma lem7222970 (m : nat) (n : nat) (p : nat) : True = (term66 m n p).
Proof. exact (SYM (@lem7222969 m n p)). Qed.
Lemma lem7222971 (m : nat) (n : nat) (p : nat) : term66 m n p.
Proof. exact (EQ_MP (@lem7222970 m n p) (@lem0)). Qed.
Lemma lem7222972 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term28 p m n f) = (term67 m n f p).
Proof. exact (@lem7222846 m n f p (@lem7222971 m n p)). Qed.
Lemma lem7222973 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term27 m n p f) = (term67 m n f p).
Proof. exact (TRANS (@lem7222842 p m n f) (@lem7222972 m n f p)). Qed.
Lemma lem7222974 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7222975 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term68 m n p f) = (term69 m n f p).
Proof. exact (MK_COMB (@lem7222974) (@lem7222973 m n f p)). Qed.
Lemma lem7222976 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term70 m n f p) = (term70 m n f p).
Proof. exact (eq_refl (term70 m n f p)). Qed.
Lemma lem7222977 (m : nat) (n : nat) (f : nat -> real) (p : nat) : ((term27 m n p f) = (term70 m n f p)) = ((term67 m n f p) = (term70 m n f p)).
Proof. exact (MK_COMB (@lem7222975 m n f p) (@lem7222976 m n f p)). Qed.
Lemma lem7222980 (m : nat) (f : nat -> real) (p : nat) : (term71 m f p) = (term72 m f p).
Proof. exact (fun_ext (fun n : nat => @lem7222977 m n f p)). Qed.
Lemma lem7222983 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7222984 (m : nat) (f : nat -> real) (p : nat) : (term73 m f p) = (term74 m f p).
Proof. exact (MK_COMB (@lem7222983) (@lem7222980 m f p)). Qed.
Lemma lem7222991 (f : nat -> real) (p : nat) : (term75 f p) = (term76 f p).
Proof. exact (fun_ext (fun m : nat => @lem7222984 m f p)). Qed.
Lemma lem7222998 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7222999 (f : nat -> real) (p : nat) : (term77 f p) = (term78 f p).
Proof. exact (MK_COMB (@lem7222998) (@lem7222991 f p)). Qed.
Lemma lem7223010 (p : nat) : (term79 p) = (term80 p).
Proof. exact (fun_ext (fun f : nat -> real => @lem7222999 f p)). Qed.
Lemma lem7223021 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7223022 (p : nat) : (term81 p) = (term82 p).
Proof. exact (MK_COMB (@lem7223021) (@lem7223010 p)). Qed.
Lemma lem7223037 : term83 = term84.
Proof. exact (fun_ext (fun p : nat => @lem7223022 p)). Qed.
Lemma lem7223052 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7223053 : term85 = term86.
Proof. exact (MK_COMB (@lem7223052) (@lem7223037)). Qed.
Lemma lem7223072 : term86 = term85.
Proof. exact (SYM (@lem7223053)). Qed.
Lemma lem7223092 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term3 A B C f g).
Proof. exact (EQ_MP (@lem7222775 A B C f g) (@lem7222774 A B C f g)). Qed.
Lemma lem7223093 (f : nat -> real) (g : nat -> nat) : (@o nat nat real f g) = (term87 f g).
Proof. exact (@lem7223092 nat nat real f g). Qed.
Lemma lem7223094 (f : nat -> real) (p : nat) : (term88 f p) = (term89 f p).
Proof. exact (@lem7223093 f (term31 p)). Qed.
Lemma lem7223096 {A B : Type'} (f : A -> B) (y : A) : (term41 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7223097 (f : nat -> nat) (y : nat) : (term42 f y) = (f y).
Proof. exact (@lem7223096 nat nat f y). Qed.
Lemma lem7223098 (p : nat) (x : nat) : (term43 p x) = (term44 p x).
Proof. exact (@lem7223097 (term31 p) x). Qed.
Lemma lem7223099 (i : nat) (p : nat) : (term44 p i) = (Nat.add i p).
Proof. exact (eq_refl (term44 p i)). Qed.
Lemma lem7223100 (p : nat) : (term45 p) = (term31 p).
Proof. exact (fun_ext (fun i : nat => @lem7223099 i p)). Qed.
Lemma lem7223101 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7223102 (p : nat) (x : nat) : (term43 p x) = (term44 p x).
Proof. exact (MK_COMB (@lem7223100 p) (@lem7223101 x)). Qed.
Lemma lem7223103 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7223104 (p : nat) (x : nat) : (term46 p x) = (term47 p x).
Proof. exact (MK_COMB (@lem7223103) (@lem7223102 p x)). Qed.
Lemma lem7223105 (x : nat) (p : nat) : (term44 p x) = (Nat.add x p).
Proof. exact (eq_refl (term44 p x)). Qed.
Lemma lem7223106 (x : nat) (p : nat) : ((term43 p x) = (term44 p x)) = ((term44 p x) = (Nat.add x p)).
Proof. exact (MK_COMB (@lem7223104 p x) (@lem7223105 x p)). Qed.
Lemma lem7223107 (x : nat) (p : nat) : (term44 p x) = (Nat.add x p).
Proof. exact (EQ_MP (@lem7223106 x p) (@lem7223098 p x)). Qed.
Lemma lem7223108 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7223109 (f : nat -> real) (x : nat) (p : nat) : (term90 f p x) = (term91 f x p).
Proof. exact (MK_COMB (@lem7223108 f) (@lem7223107 x p)). Qed.
Lemma lem7223110 (f : nat -> real) (p : nat) : (term89 f p) = (term92 f p).
Proof. exact (fun_ext (fun x : nat => @lem7223109 f x p)). Qed.
Lemma lem7223111 (f : nat -> real) (p : nat) : (term88 f p) = (term92 f p).
Proof. exact (TRANS (@lem7223094 f p) (@lem7223110 f p)). Qed.
Lemma lem7223112 (m : nat) (n : nat) : (term93 m n) = (term93 m n).
Proof. exact (eq_refl (term93 m n)). Qed.
Lemma lem7223113 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term67 m n f p) = (term70 m n f p).
Proof. exact (MK_COMB (@lem7223112 m n) (@lem7223111 f p)). Qed.
Lemma lem7223114 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7223115 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term69 m n f p) = (term94 m n f p).
Proof. exact (MK_COMB (@lem7223114) (@lem7223113 m n f p)). Qed.
Lemma lem7223116 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term70 m n f p) = (term70 m n f p).
Proof. exact (eq_refl (term70 m n f p)). Qed.
Lemma lem7223117 (m : nat) (n : nat) (f : nat -> real) (p : nat) : ((term67 m n f p) = (term70 m n f p)) = ((term70 m n f p) = (term70 m n f p)).
Proof. exact (MK_COMB (@lem7223115 m n f p) (@lem7223116 m n f p)). Qed.
Lemma lem7223119 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7223120 (x : real) : (x = x) = True.
Proof. exact (@lem7223119 real x). Qed.
Lemma lem7223121 (m : nat) (n : nat) (f : nat -> real) (p : nat) : ((term70 m n f p) = (term70 m n f p)) = True.
Proof. exact (@lem7223120 (term70 m n f p)). Qed.
Lemma lem7223124 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term95 m n f p) = (term95 m n f p).
Proof. exact (eq_refl (term95 m n f p)). Qed.
Lemma lem7223125 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term95 m n f p) = (((term70 m n f p) = (term70 m n f p)) = True).
Proof. exact (eq_refl (term95 m n f p)). Qed.
Lemma lem7223126 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term96 m n f p) = (term96 m n f p).
Proof. exact (eq_refl (term96 m n f p)). Qed.
Lemma lem7223127 (m : nat) (n : nat) (f : nat -> real) (p : nat) : ((term95 m n f p) = (term95 m n f p)) = ((term95 m n f p) = (((term70 m n f p) = (term70 m n f p)) = True)).
Proof. exact (MK_COMB (@lem7223126 m n f p) (@lem7223125 m n f p)). Qed.
Lemma lem7223128 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term95 m n f p) = (((term70 m n f p) = (term70 m n f p)) = True).
Proof. exact (eq_refl (term95 m n f p)). Qed.
Lemma lem7223129 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7223130 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term96 m n f p) = (term97 m n f p).
Proof. exact (MK_COMB (@lem7223129) (@lem7223128 m n f p)). Qed.
Lemma lem7223131 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (((term70 m n f p) = (term70 m n f p)) = True) = (((term70 m n f p) = (term70 m n f p)) = True).
Proof. exact (eq_refl (((term70 m n f p) = (term70 m n f p)) = True)). Qed.
Lemma lem7223132 (m : nat) (n : nat) (f : nat -> real) (p : nat) : ((term95 m n f p) = (((term70 m n f p) = (term70 m n f p)) = True)) = ((((term70 m n f p) = (term70 m n f p)) = True) = (((term70 m n f p) = (term70 m n f p)) = True)).
Proof. exact (MK_COMB (@lem7223130 m n f p) (@lem7223131 m n f p)). Qed.
Lemma lem7223133 (m : nat) (n : nat) (f : nat -> real) (p : nat) : ((term95 m n f p) = (term95 m n f p)) = ((((term70 m n f p) = (term70 m n f p)) = True) = (((term70 m n f p) = (term70 m n f p)) = True)).
Proof. exact (TRANS (@lem7223127 m n f p) (@lem7223132 m n f p)). Qed.
Lemma lem7223134 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (((term70 m n f p) = (term70 m n f p)) = True) = (((term70 m n f p) = (term70 m n f p)) = True).
Proof. exact (EQ_MP (@lem7223133 m n f p) (@lem7223124 m n f p)). Qed.
Lemma lem7223135 (m : nat) (n : nat) (f : nat -> real) (p : nat) : ((term70 m n f p) = (term70 m n f p)) = True.
Proof. exact (EQ_MP (@lem7223134 m n f p) (@lem7223121 m n f p)). Qed.
Lemma lem7223136 (m : nat) (n : nat) (f : nat -> real) (p : nat) : ((term67 m n f p) = (term70 m n f p)) = True.
Proof. exact (TRANS (@lem7223117 m n f p) (@lem7223135 m n f p)). Qed.
Lemma lem7223137 (m : nat) (f : nat -> real) (p : nat) : (term72 m f p) = term60.
Proof. exact (fun_ext (fun n : nat => @lem7223136 m n f p)). Qed.
Lemma lem7223138 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7223139 (m : nat) (f : nat -> real) (p : nat) : (term74 m f p) = term62.
Proof. exact (MK_COMB (@lem7223138) (@lem7223137 m f p)). Qed.
Lemma lem7223141 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7223142 (t : Prop) : (term64 t) = t.
Proof. exact (@lem7223141 nat t). Qed.
Lemma lem7223143 : term62 = True.
Proof. exact (@lem7223142 True). Qed.
Lemma lem7223144 (m : nat) (f : nat -> real) (p : nat) : (term74 m f p) = True.
Proof. exact (TRANS (@lem7223139 m f p) (@lem7223143)). Qed.
Lemma lem7223145 (f : nat -> real) (p : nat) : (term76 f p) = term60.
Proof. exact (fun_ext (fun m : nat => @lem7223144 m f p)). Qed.
Lemma lem7223146 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7223147 (f : nat -> real) (p : nat) : (term78 f p) = term62.
Proof. exact (MK_COMB (@lem7223146) (@lem7223145 f p)). Qed.
Lemma lem7223149 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7223150 (t : Prop) : (term64 t) = t.
Proof. exact (@lem7223149 nat t). Qed.
Lemma lem7223151 : term62 = True.
Proof. exact (@lem7223150 True). Qed.
Lemma lem7223152 (f : nat -> real) (p : nat) : (term78 f p) = True.
Proof. exact (TRANS (@lem7223147 f p) (@lem7223151)). Qed.
Lemma lem7223153 (p : nat) : (term80 p) = term98.
Proof. exact (fun_ext (fun f : nat -> real => @lem7223152 f p)). Qed.
Lemma lem7223154 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7223155 (p : nat) : (term82 p) = term99.
Proof. exact (MK_COMB (@lem7223154) (@lem7223153 p)). Qed.
Lemma lem7223157 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7223158 (t : Prop) : (term100 t) = t.
Proof. exact (@lem7223157 (nat -> real) t). Qed.
Lemma lem7223159 : term99 = True.
Proof. exact (@lem7223158 True). Qed.
Lemma lem7223160 (p : nat) : (term82 p) = True.
Proof. exact (TRANS (@lem7223155 p) (@lem7223159)). Qed.
Lemma lem7223161 : term84 = term60.
Proof. exact (fun_ext (fun p : nat => @lem7223160 p)). Qed.
Lemma lem7223162 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7223163 : term86 = term62.
Proof. exact (MK_COMB (@lem7223162) (@lem7223161)). Qed.
Lemma lem7223165 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7223166 (t : Prop) : (term64 t) = t.
Proof. exact (@lem7223165 nat t). Qed.
Lemma lem7223167 : term62 = True.
Proof. exact (@lem7223166 True). Qed.
Lemma lem7223168 : term86 = True.
Proof. exact (TRANS (@lem7223163) (@lem7223167)). Qed.
Lemma lem7223169 : True = term86.
Proof. exact (SYM (@lem7223168)). Qed.
Lemma lem7223170 : term86.
Proof. exact (EQ_MP (@lem7223169) (@lem0)). Qed.
Lemma lem7223171 : term85.
Proof. exact (EQ_MP (@lem7223072) (@lem7223170)). Qed.
