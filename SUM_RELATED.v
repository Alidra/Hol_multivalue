Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_RELATED_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import ITERATE_RELATED_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import sum_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
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
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm7_spec.
Require Import thm7064171_spec.
Require Import thm7065437_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem7199889 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7199890 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7199891 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7199890 t1) (@lem7199889 t1)). Qed.
Lemma lem7199892 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7199891 t1 t2). Qed.
Lemma lem7199893 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7199894 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7199893 t1 t2) (@lem7199892 t1 t2)). Qed.
Lemma lem7199895 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7199894 t1 t2 t3). Qed.
Lemma lem7199896 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7199897 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7199896 t1 t2 t3) (@lem7199895 t1 t2 t3)). Qed.
Lemma lem7199898 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7199897 t1 t2 t3)). Qed.
Lemma lem7199899 {_131408 : Type'} (h1 : (@sum _131408) = (@iterate real _131408 real_add)) : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (h1). Qed.
Lemma lem7199900 {_131408 : Type'} (h1 : (@sum _131408) = (@iterate real _131408 real_add)) : (@iterate real _131408 real_add) = (@sum _131408).
Proof. exact (SYM (@lem7199899 _131408 h1)). Qed.
Lemma lem7199901 {_131408 : Type'} (h1 : (@iterate real _131408 real_add) = (@sum _131408)) : (@iterate real _131408 real_add) = (@sum _131408).
Proof. exact (h1). Qed.
Lemma lem7199902 {_131408 : Type'} (h1 : (@iterate real _131408 real_add) = (@sum _131408)) : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (SYM (@lem7199901 _131408 h1)). Qed.
Lemma lem7199903 {_131408 : Type'} : ((@sum _131408) = (@iterate real _131408 real_add)) = ((@iterate real _131408 real_add) = (@sum _131408)).
Proof. exact (prop_ext (fun h1 : (@sum _131408) = (@iterate real _131408 real_add) => @lem7199900 _131408 h1) (fun h1 : (@iterate real _131408 real_add) = (@sum _131408) => @lem7199902 _131408 h1)). Qed.
Lemma lem7199905 {A B : Type'} (op : type1400 B) : term7 A B op.
Proof. exact (@lem5783455 A B op). Qed.
Lemma lem7199906 {A B : Type'} (op : type1400 B) : (term7 A B op) = (term8 A B op).
Proof. exact (eq_refl (term7 A B op)). Qed.
Lemma lem7199909 {A B : Type'} (op : type1400 B) : term8 A B op.
Proof. exact (EQ_MP (@lem7199906 A B op) (@lem7199905 A B op)). Qed.
Lemma lem7199910 {A : Type'} (op : type1627) : term9 A op.
Proof. exact (@lem7199909 A real op). Qed.
Lemma lem7199911 {A : Type'} : term10 A.
Proof. exact (@lem7199910 A real_add). Qed.
Lemma lem7199912 {A : Type'} : term11 A.
Proof. exact (@lem7199911 A (@lem7067132)). Qed.
Lemma lem7199913 {A : Type'} (R : type1626) : term12 A R.
Proof. exact (@lem7199912 A R). Qed.
Lemma lem7199914 {A : Type'} (R : type1626) : (term12 A R) = (term13 A R).
Proof. exact (eq_refl (term12 A R)). Qed.
Lemma lem7199915 {A : Type'} (R : type1626) : term13 A R.
Proof. exact (EQ_MP (@lem7199914 A R) (@lem7199913 A R)). Qed.
Lemma lem7199916 {A : Type'} (P : Prop) : term14 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem7199917 {A : Type'} (P : Prop) : (term14 A P) = (term15 A P).
Proof. exact (eq_refl (term14 A P)). Qed.
Lemma lem7199918 {A : Type'} (P : Prop) : term15 A P.
Proof. exact (EQ_MP (@lem7199917 A P) (@lem7199916 A P)). Qed.
Lemma lem7199919 {A : Type'} (P : Prop) (Q : A -> Prop) : term16 A P Q.
Proof. exact (@lem7199918 A P Q). Qed.
Lemma lem7199920 {A : Type'} (P : Prop) (Q : A -> Prop) : (term16 A P Q) = ((term17 A P Q) = (term18 A P Q)).
Proof. exact (eq_refl (term16 A P Q)). Qed.
Lemma lem7199959 (p : Prop) (q : Prop) (r : Prop) : (term19 p q r) = (term20 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7199960 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term21 A R f s g) = (term22 A R f s g).
Proof. exact (@lem7199959 (term23 R) (term24 A s R f g) (term25 A R f s g)). Qed.
Lemma lem7199964 (p : Prop) (q : Prop) (r : Prop) : (term19 p q r) = (term20 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7199965 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term26 A R f s g) = (term27 A R f s g).
Proof. exact (@lem7199964 (term28 R) (term29 A s R f g) (term25 A R f s g)). Qed.
Lemma lem7200005 (p : Prop) (q : Prop) (r : Prop) : (term19 p q r) = (term20 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7200006 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term30 R m m' n n') = (term31 R m m' n n').
Proof. exact (@lem7200005 (R m n) (R m' n') (term32 R m m' n n')). Qed.
Lemma lem7200011 (R : type1626) (m : real) (m' : real) (n : real) : (term33 R m m' n) = (term34 R m m' n).
Proof. exact (fun_ext (fun n' : real => @lem7200006 R m m' n n')). Qed.
Lemma lem7200012 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7200013 (R : type1626) (m : real) (m' : real) (n : real) : (term35 R m m' n) = (term36 R m m' n).
Proof. exact (MK_COMB (@lem7200012) (@lem7200011 R m m' n)). Qed.
Lemma lem7200015 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7199920 A P Q) (@lem7199919 A P Q)). Qed.
Lemma lem7200016 (P : Prop) (Q : real -> Prop) : (term37 P Q) = (term38 P Q).
Proof. exact (@lem7200015 real P Q). Qed.
Lemma lem7200017 (R : type1626) (m : real) (m' : real) (n : real) : (term39 R m m' n) = (term40 R m m' n).
Proof. exact (@lem7200016 (R m n) (term41 R m m' n)). Qed.
Lemma lem7200018 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term42 R m m' n n') = (term43 R m m' n n').
Proof. exact (eq_refl (term42 R m m' n n')). Qed.
Lemma lem7200019 (R : type1626) (m : real) (n : real) : (term44 R m n) = (term44 R m n).
Proof. exact (eq_refl (term44 R m n)). Qed.
Lemma lem7200020 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term45 R m m' n n') = (term31 R m m' n n').
Proof. exact (MK_COMB (@lem7200019 R m n) (@lem7200018 R m m' n n')). Qed.
Lemma lem7200021 (R : type1626) (m : real) (m' : real) (n : real) : (term46 R m m' n) = (term34 R m m' n).
Proof. exact (fun_ext (fun n' : real => @lem7200020 R m m' n n')). Qed.
Lemma lem7200022 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7200023 (R : type1626) (m : real) (m' : real) (n : real) : (term39 R m m' n) = (term36 R m m' n).
Proof. exact (MK_COMB (@lem7200022) (@lem7200021 R m m' n)). Qed.
Lemma lem7200024 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7200025 (R : type1626) (m : real) (m' : real) (n : real) : (term47 R m m' n) = (term48 R m m' n).
Proof. exact (MK_COMB (@lem7200024) (@lem7200023 R m m' n)). Qed.
Lemma lem7200026 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term42 R m m' n n') = (term43 R m m' n n').
Proof. exact (eq_refl (term42 R m m' n n')). Qed.
Lemma lem7200027 (R : type1626) (m : real) (m' : real) (n : real) : (term49 R m m' n) = (term41 R m m' n).
Proof. exact (fun_ext (fun n' : real => @lem7200026 R m m' n n')). Qed.
Lemma lem7200028 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7200029 (R : type1626) (m : real) (m' : real) (n : real) : (term50 R m m' n) = (term51 R m m' n).
Proof. exact (MK_COMB (@lem7200028) (@lem7200027 R m m' n)). Qed.
Lemma lem7200030 (R : type1626) (m : real) (n : real) : (term44 R m n) = (term44 R m n).
Proof. exact (eq_refl (term44 R m n)). Qed.
Lemma lem7200031 (R : type1626) (m : real) (m' : real) (n : real) : (term40 R m m' n) = (term52 R m m' n).
Proof. exact (MK_COMB (@lem7200030 R m n) (@lem7200029 R m m' n)). Qed.
Lemma lem7200032 (R : type1626) (m : real) (m' : real) (n : real) : ((term39 R m m' n) = (term40 R m m' n)) = ((term36 R m m' n) = (term52 R m m' n)).
Proof. exact (MK_COMB (@lem7200025 R m m' n) (@lem7200031 R m m' n)). Qed.
Lemma lem7200033 (R : type1626) (m : real) (m' : real) (n : real) : (term36 R m m' n) = (term52 R m m' n).
Proof. exact (EQ_MP (@lem7200032 R m m' n) (@lem7200017 R m m' n)). Qed.
Lemma lem7200062 (R : type1626) (m : real) (m' : real) (n : real) : (term35 R m m' n) = (term52 R m m' n).
Proof. exact (TRANS (@lem7200013 R m m' n) (@lem7200033 R m m' n)). Qed.
Lemma lem7200063 (R : type1626) (m : real) (n : real) : (term53 R m n) = (term54 R m n).
Proof. exact (fun_ext (fun m' : real => @lem7200062 R m m' n)). Qed.
Lemma lem7200064 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7200065 (R : type1626) (m : real) (n : real) : (term55 R m n) = (term56 R m n).
Proof. exact (MK_COMB (@lem7200064) (@lem7200063 R m n)). Qed.
Lemma lem7200067 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7199920 A P Q) (@lem7199919 A P Q)). Qed.
Lemma lem7200068 (P : Prop) (Q : real -> Prop) : (term37 P Q) = (term38 P Q).
Proof. exact (@lem7200067 real P Q). Qed.
Lemma lem7200069 (R : type1626) (m : real) (n : real) : (term57 R m n) = (term58 R m n).
Proof. exact (@lem7200068 (R m n) (term59 R m n)). Qed.
Lemma lem7200070 (R : type1626) (m : real) (m' : real) (n : real) : (term60 R m n m') = (term51 R m m' n).
Proof. exact (eq_refl (term60 R m n m')). Qed.
Lemma lem7200071 (R : type1626) (m : real) (n : real) : (term44 R m n) = (term44 R m n).
Proof. exact (eq_refl (term44 R m n)). Qed.
Lemma lem7200072 (R : type1626) (m : real) (m' : real) (n : real) : (term61 R m n m') = (term52 R m m' n).
Proof. exact (MK_COMB (@lem7200071 R m n) (@lem7200070 R m m' n)). Qed.
Lemma lem7200073 (R : type1626) (m : real) (n : real) : (term62 R m n) = (term54 R m n).
Proof. exact (fun_ext (fun m' : real => @lem7200072 R m m' n)). Qed.
Lemma lem7200074 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7200075 (R : type1626) (m : real) (n : real) : (term57 R m n) = (term56 R m n).
Proof. exact (MK_COMB (@lem7200074) (@lem7200073 R m n)). Qed.
Lemma lem7200076 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7200077 (R : type1626) (m : real) (n : real) : (term63 R m n) = (term64 R m n).
Proof. exact (MK_COMB (@lem7200076) (@lem7200075 R m n)). Qed.
Lemma lem7200078 (R : type1626) (m : real) (m' : real) (n : real) : (term60 R m n m') = (term51 R m m' n).
Proof. exact (eq_refl (term60 R m n m')). Qed.
Lemma lem7200079 (R : type1626) (m : real) (n : real) : (term65 R m n) = (term59 R m n).
Proof. exact (fun_ext (fun m' : real => @lem7200078 R m m' n)). Qed.
Lemma lem7200080 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7200081 (R : type1626) (m : real) (n : real) : (term66 R m n) = (term67 R m n).
Proof. exact (MK_COMB (@lem7200080) (@lem7200079 R m n)). Qed.
Lemma lem7200082 (R : type1626) (m : real) (n : real) : (term44 R m n) = (term44 R m n).
Proof. exact (eq_refl (term44 R m n)). Qed.
Lemma lem7200083 (R : type1626) (m : real) (n : real) : (term58 R m n) = (term68 R m n).
Proof. exact (MK_COMB (@lem7200082 R m n) (@lem7200081 R m n)). Qed.
Lemma lem7200084 (R : type1626) (m : real) (n : real) : ((term57 R m n) = (term58 R m n)) = ((term56 R m n) = (term68 R m n)).
Proof. exact (MK_COMB (@lem7200077 R m n) (@lem7200083 R m n)). Qed.
Lemma lem7200085 (R : type1626) (m : real) (n : real) : (term56 R m n) = (term68 R m n).
Proof. exact (EQ_MP (@lem7200084 R m n) (@lem7200069 R m n)). Qed.
Lemma lem7200118 (R : type1626) (m : real) (n : real) : (term55 R m n) = (term68 R m n).
Proof. exact (TRANS (@lem7200065 R m n) (@lem7200085 R m n)). Qed.
Lemma lem7200119 (R : type1626) (m : real) : (term69 R m) = (term70 R m).
Proof. exact (fun_ext (fun n : real => @lem7200118 R m n)). Qed.
Lemma lem7200120 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7200121 (R : type1626) (m : real) : (term71 R m) = (term72 R m).
Proof. exact (MK_COMB (@lem7200120) (@lem7200119 R m)). Qed.
Lemma lem7200146 (R : type1626) : (term73 R) = (term74 R).
Proof. exact (fun_ext (fun m : real => @lem7200121 R m)). Qed.
Lemma lem7200147 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7200148 (R : type1626) : (term28 R) = (term75 R).
Proof. exact (MK_COMB (@lem7200147) (@lem7200146 R)). Qed.
Lemma lem7200153 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7200154 (R : type1626) : (term76 R) = (term77 R).
Proof. exact (MK_COMB (@lem7200153) (@lem7200148 R)). Qed.
Lemma lem7200156 (p : Prop) (q : Prop) (r : Prop) : (term19 p q r) = (term20 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7200157 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term78 A R f s g) = (term79 A R f s g).
Proof. exact (@lem7200156 (@FINITE A s) (term80 A s R f g) (term25 A R f s g)). Qed.
Lemma lem7200188 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term27 A R f s g) = (term81 A R f s g).
Proof. exact (MK_COMB (@lem7200154 R) (@lem7200157 A R f s g)). Qed.
Lemma lem7200191 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term26 A R f s g) = (term81 A R f s g).
Proof. exact (TRANS (@lem7199965 A R f s g) (@lem7200188 A R f s g)). Qed.
Lemma lem7200192 (R : type1626) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7200193 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term22 A R f s g) = (term83 A R f s g).
Proof. exact (MK_COMB (@lem7200192 R) (@lem7200191 A R f s g)). Qed.
Lemma lem7200196 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term21 A R f s g) = (term83 A R f s g).
Proof. exact (TRANS (@lem7199960 A R f s g) (@lem7200193 A R f s g)). Qed.
Lemma lem7200197 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term84 A R f g) = (term85 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7200196 A R f s g)). Qed.
Lemma lem7200198 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7200199 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term86 A R f g) = (term87 A R f g).
Proof. exact (MK_COMB (@lem7200198 A) (@lem7200197 A R f g)). Qed.
Lemma lem7200201 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7199920 A P Q) (@lem7199919 A P Q)). Qed.
Lemma lem7200202 {A : Type'} (P : Prop) (Q : type686 A) : (term88 A P Q) = (term89 A P Q).
Proof. exact (@lem7200201 (A -> Prop) P Q). Qed.
Lemma lem7200203 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term90 A R f g) = (term91 A R f g).
Proof. exact (@lem7200202 A (term23 R) (term92 A R f g)). Qed.
Lemma lem7200204 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term93 A R f g s) = (term81 A R f s g).
Proof. exact (eq_refl (term93 A R f g s)). Qed.
Lemma lem7200205 (R : type1626) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7200206 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term94 A R f g s) = (term83 A R f s g).
Proof. exact (MK_COMB (@lem7200205 R) (@lem7200204 A R f s g)). Qed.
Lemma lem7200207 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term95 A R f g) = (term85 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7200206 A R f s g)). Qed.
Lemma lem7200208 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7200209 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term90 A R f g) = (term87 A R f g).
Proof. exact (MK_COMB (@lem7200208 A) (@lem7200207 A R f g)). Qed.
Lemma lem7200210 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7200211 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term96 A R f g) = (term97 A R f g).
Proof. exact (MK_COMB (@lem7200210) (@lem7200209 A R f g)). Qed.
Lemma lem7200212 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term93 A R f g s) = (term81 A R f s g).
Proof. exact (eq_refl (term93 A R f g s)). Qed.
Lemma lem7200213 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term98 A R f g) = (term92 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7200212 A R f s g)). Qed.
Lemma lem7200214 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7200215 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term99 A R f g) = (term100 A R f g).
Proof. exact (MK_COMB (@lem7200214 A) (@lem7200213 A R f g)). Qed.
Lemma lem7200216 (R : type1626) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7200217 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term91 A R f g) = (term101 A R f g).
Proof. exact (MK_COMB (@lem7200216 R) (@lem7200215 A R f g)). Qed.
Lemma lem7200218 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : ((term90 A R f g) = (term91 A R f g)) = ((term87 A R f g) = (term101 A R f g)).
Proof. exact (MK_COMB (@lem7200211 A R f g) (@lem7200217 A R f g)). Qed.
Lemma lem7200219 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term87 A R f g) = (term101 A R f g).
Proof. exact (EQ_MP (@lem7200218 A R f g) (@lem7200203 A R f g)). Qed.
Lemma lem7200223 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7199920 A P Q) (@lem7199919 A P Q)). Qed.
Lemma lem7200224 {A : Type'} (P : Prop) (Q : type686 A) : (term88 A P Q) = (term89 A P Q).
Proof. exact (@lem7200223 (A -> Prop) P Q). Qed.
Lemma lem7200225 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term102 A R f g) = (term103 A R f g).
Proof. exact (@lem7200224 A (term75 R) (term104 A R f g)). Qed.
Lemma lem7200226 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term105 A R f g s) = (term79 A R f s g).
Proof. exact (eq_refl (term105 A R f g s)). Qed.
Lemma lem7200227 (R : type1626) : (term77 R) = (term77 R).
Proof. exact (eq_refl (term77 R)). Qed.
Lemma lem7200228 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term106 A R f g s) = (term81 A R f s g).
Proof. exact (MK_COMB (@lem7200227 R) (@lem7200226 A R f s g)). Qed.
Lemma lem7200229 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term107 A R f g) = (term92 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7200228 A R f s g)). Qed.
Lemma lem7200230 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7200231 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term102 A R f g) = (term100 A R f g).
Proof. exact (MK_COMB (@lem7200230 A) (@lem7200229 A R f g)). Qed.
Lemma lem7200232 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7200233 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term108 A R f g) = (term109 A R f g).
Proof. exact (MK_COMB (@lem7200232) (@lem7200231 A R f g)). Qed.
Lemma lem7200234 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term105 A R f g s) = (term79 A R f s g).
Proof. exact (eq_refl (term105 A R f g s)). Qed.
Lemma lem7200235 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term110 A R f g) = (term104 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7200234 A R f s g)). Qed.
Lemma lem7200236 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7200237 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term111 A R f g) = (term112 A R f g).
Proof. exact (MK_COMB (@lem7200236 A) (@lem7200235 A R f g)). Qed.
Lemma lem7200238 (R : type1626) : (term77 R) = (term77 R).
Proof. exact (eq_refl (term77 R)). Qed.
Lemma lem7200239 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term103 A R f g) = (term113 A R f g).
Proof. exact (MK_COMB (@lem7200238 R) (@lem7200237 A R f g)). Qed.
Lemma lem7200240 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : ((term102 A R f g) = (term103 A R f g)) = ((term100 A R f g) = (term113 A R f g)).
Proof. exact (MK_COMB (@lem7200233 A R f g) (@lem7200239 A R f g)). Qed.
Lemma lem7200241 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term100 A R f g) = (term113 A R f g).
Proof. exact (EQ_MP (@lem7200240 A R f g) (@lem7200225 A R f g)). Qed.
Lemma lem7200358 (R : type1626) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7200359 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term101 A R f g) = (term114 A R f g).
Proof. exact (MK_COMB (@lem7200358 R) (@lem7200241 A R f g)). Qed.
Lemma lem7200362 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term87 A R f g) = (term114 A R f g).
Proof. exact (TRANS (@lem7200219 A R f g) (@lem7200359 A R f g)). Qed.
Lemma lem7200363 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term86 A R f g) = (term114 A R f g).
Proof. exact (TRANS (@lem7200199 A R f g) (@lem7200362 A R f g)). Qed.
Lemma lem7200364 {A : Type'} (R : type1626) (f : A -> real) : (term115 A R f) = (term116 A R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7200363 A R f g)). Qed.
Lemma lem7200365 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7200366 {A : Type'} (R : type1626) (f : A -> real) : (term117 A R f) = (term118 A R f).
Proof. exact (MK_COMB (@lem7200365 A) (@lem7200364 A R f)). Qed.
Lemma lem7200368 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7199920 A P Q) (@lem7199919 A P Q)). Qed.
Lemma lem7200369 {A : Type'} (P : Prop) (Q : type716 A) : (term119 A P Q) = (term120 A P Q).
Proof. exact (@lem7200368 (A -> real) P Q). Qed.
Lemma lem7200370 {A : Type'} (R : type1626) (f : A -> real) : (term121 A R f) = (term122 A R f).
Proof. exact (@lem7200369 A (term23 R) (term123 A R f)). Qed.
Lemma lem7200371 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term124 A R f g) = (term113 A R f g).
Proof. exact (eq_refl (term124 A R f g)). Qed.
Lemma lem7200372 (R : type1626) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7200373 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term125 A R f g) = (term114 A R f g).
Proof. exact (MK_COMB (@lem7200372 R) (@lem7200371 A R f g)). Qed.
Lemma lem7200374 {A : Type'} (R : type1626) (f : A -> real) : (term126 A R f) = (term116 A R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7200373 A R f g)). Qed.
Lemma lem7200375 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7200376 {A : Type'} (R : type1626) (f : A -> real) : (term121 A R f) = (term118 A R f).
Proof. exact (MK_COMB (@lem7200375 A) (@lem7200374 A R f)). Qed.
Lemma lem7200377 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7200378 {A : Type'} (R : type1626) (f : A -> real) : (term127 A R f) = (term128 A R f).
Proof. exact (MK_COMB (@lem7200377) (@lem7200376 A R f)). Qed.
Lemma lem7200379 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term124 A R f g) = (term113 A R f g).
Proof. exact (eq_refl (term124 A R f g)). Qed.
Lemma lem7200380 {A : Type'} (R : type1626) (f : A -> real) : (term129 A R f) = (term123 A R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7200379 A R f g)). Qed.
Lemma lem7200381 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7200382 {A : Type'} (R : type1626) (f : A -> real) : (term130 A R f) = (term131 A R f).
Proof. exact (MK_COMB (@lem7200381 A) (@lem7200380 A R f)). Qed.
Lemma lem7200383 (R : type1626) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7200384 {A : Type'} (R : type1626) (f : A -> real) : (term122 A R f) = (term132 A R f).
Proof. exact (MK_COMB (@lem7200383 R) (@lem7200382 A R f)). Qed.
Lemma lem7200385 {A : Type'} (R : type1626) (f : A -> real) : ((term121 A R f) = (term122 A R f)) = ((term118 A R f) = (term132 A R f)).
Proof. exact (MK_COMB (@lem7200378 A R f) (@lem7200384 A R f)). Qed.
Lemma lem7200386 {A : Type'} (R : type1626) (f : A -> real) : (term118 A R f) = (term132 A R f).
Proof. exact (EQ_MP (@lem7200385 A R f) (@lem7200370 A R f)). Qed.
Lemma lem7200390 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7199920 A P Q) (@lem7199919 A P Q)). Qed.
Lemma lem7200391 {A : Type'} (P : Prop) (Q : type716 A) : (term119 A P Q) = (term120 A P Q).
Proof. exact (@lem7200390 (A -> real) P Q). Qed.
Lemma lem7200392 {A : Type'} (R : type1626) (f : A -> real) : (term133 A R f) = (term134 A R f).
Proof. exact (@lem7200391 A (term75 R) (term135 A R f)). Qed.
Lemma lem7200393 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term136 A R f g) = (term112 A R f g).
Proof. exact (eq_refl (term136 A R f g)). Qed.
Lemma lem7200394 (R : type1626) : (term77 R) = (term77 R).
Proof. exact (eq_refl (term77 R)). Qed.
Lemma lem7200395 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term137 A R f g) = (term113 A R f g).
Proof. exact (MK_COMB (@lem7200394 R) (@lem7200393 A R f g)). Qed.
Lemma lem7200396 {A : Type'} (R : type1626) (f : A -> real) : (term138 A R f) = (term123 A R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7200395 A R f g)). Qed.
Lemma lem7200397 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7200398 {A : Type'} (R : type1626) (f : A -> real) : (term133 A R f) = (term131 A R f).
Proof. exact (MK_COMB (@lem7200397 A) (@lem7200396 A R f)). Qed.
Lemma lem7200399 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7200400 {A : Type'} (R : type1626) (f : A -> real) : (term139 A R f) = (term140 A R f).
Proof. exact (MK_COMB (@lem7200399) (@lem7200398 A R f)). Qed.
Lemma lem7200401 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term136 A R f g) = (term112 A R f g).
Proof. exact (eq_refl (term136 A R f g)). Qed.
Lemma lem7200402 {A : Type'} (R : type1626) (f : A -> real) : (term141 A R f) = (term135 A R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7200401 A R f g)). Qed.
Lemma lem7200403 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7200404 {A : Type'} (R : type1626) (f : A -> real) : (term142 A R f) = (term143 A R f).
Proof. exact (MK_COMB (@lem7200403 A) (@lem7200402 A R f)). Qed.
Lemma lem7200405 (R : type1626) : (term77 R) = (term77 R).
Proof. exact (eq_refl (term77 R)). Qed.
Lemma lem7200406 {A : Type'} (R : type1626) (f : A -> real) : (term134 A R f) = (term144 A R f).
Proof. exact (MK_COMB (@lem7200405 R) (@lem7200404 A R f)). Qed.
Lemma lem7200407 {A : Type'} (R : type1626) (f : A -> real) : ((term133 A R f) = (term134 A R f)) = ((term131 A R f) = (term144 A R f)).
Proof. exact (MK_COMB (@lem7200400 A R f) (@lem7200406 A R f)). Qed.
Lemma lem7200408 {A : Type'} (R : type1626) (f : A -> real) : (term131 A R f) = (term144 A R f).
Proof. exact (EQ_MP (@lem7200407 A R f) (@lem7200392 A R f)). Qed.
Lemma lem7200529 (R : type1626) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7200530 {A : Type'} (R : type1626) (f : A -> real) : (term132 A R f) = (term145 A R f).
Proof. exact (MK_COMB (@lem7200529 R) (@lem7200408 A R f)). Qed.
Lemma lem7200533 {A : Type'} (R : type1626) (f : A -> real) : (term118 A R f) = (term145 A R f).
Proof. exact (TRANS (@lem7200386 A R f) (@lem7200530 A R f)). Qed.
Lemma lem7200534 {A : Type'} (R : type1626) (f : A -> real) : (term117 A R f) = (term145 A R f).
Proof. exact (TRANS (@lem7200366 A R f) (@lem7200533 A R f)). Qed.
Lemma lem7200535 {A : Type'} (R : type1626) : (term146 A R) = (term147 A R).
Proof. exact (fun_ext (fun f : A -> real => @lem7200534 A R f)). Qed.
Lemma lem7200536 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7200537 {A : Type'} (R : type1626) : (term148 A R) = (term149 A R).
Proof. exact (MK_COMB (@lem7200536 A) (@lem7200535 A R)). Qed.
Lemma lem7200539 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7199920 A P Q) (@lem7199919 A P Q)). Qed.
Lemma lem7200540 {A : Type'} (P : Prop) (Q : type716 A) : (term119 A P Q) = (term120 A P Q).
Proof. exact (@lem7200539 (A -> real) P Q). Qed.
Lemma lem7200541 {A : Type'} (R : type1626) : (term150 A R) = (term151 A R).
Proof. exact (@lem7200540 A (term23 R) (term152 A R)). Qed.
Lemma lem7200542 {A : Type'} (R : type1626) (f : A -> real) : (term153 A R f) = (term144 A R f).
Proof. exact (eq_refl (term153 A R f)). Qed.
Lemma lem7200543 (R : type1626) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7200544 {A : Type'} (R : type1626) (f : A -> real) : (term154 A R f) = (term145 A R f).
Proof. exact (MK_COMB (@lem7200543 R) (@lem7200542 A R f)). Qed.
Lemma lem7200545 {A : Type'} (R : type1626) : (term155 A R) = (term147 A R).
Proof. exact (fun_ext (fun f : A -> real => @lem7200544 A R f)). Qed.
Lemma lem7200546 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7200547 {A : Type'} (R : type1626) : (term150 A R) = (term149 A R).
Proof. exact (MK_COMB (@lem7200546 A) (@lem7200545 A R)). Qed.
Lemma lem7200548 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7200549 {A : Type'} (R : type1626) : (term156 A R) = (term157 A R).
Proof. exact (MK_COMB (@lem7200548) (@lem7200547 A R)). Qed.
Lemma lem7200550 {A : Type'} (R : type1626) (f : A -> real) : (term153 A R f) = (term144 A R f).
Proof. exact (eq_refl (term153 A R f)). Qed.
Lemma lem7200551 {A : Type'} (R : type1626) : (term158 A R) = (term152 A R).
Proof. exact (fun_ext (fun f : A -> real => @lem7200550 A R f)). Qed.
Lemma lem7200552 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7200553 {A : Type'} (R : type1626) : (term159 A R) = (term160 A R).
Proof. exact (MK_COMB (@lem7200552 A) (@lem7200551 A R)). Qed.
Lemma lem7200554 (R : type1626) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7200555 {A : Type'} (R : type1626) : (term151 A R) = (term161 A R).
Proof. exact (MK_COMB (@lem7200554 R) (@lem7200553 A R)). Qed.
Lemma lem7200556 {A : Type'} (R : type1626) : ((term150 A R) = (term151 A R)) = ((term149 A R) = (term161 A R)).
Proof. exact (MK_COMB (@lem7200549 A R) (@lem7200555 A R)). Qed.
Lemma lem7200557 {A : Type'} (R : type1626) : (term149 A R) = (term161 A R).
Proof. exact (EQ_MP (@lem7200556 A R) (@lem7200541 A R)). Qed.
Lemma lem7200561 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem7199920 A P Q) (@lem7199919 A P Q)). Qed.
Lemma lem7200562 {A : Type'} (P : Prop) (Q : type716 A) : (term119 A P Q) = (term120 A P Q).
Proof. exact (@lem7200561 (A -> real) P Q). Qed.
Lemma lem7200563 {A : Type'} (R : type1626) : (term162 A R) = (term163 A R).
Proof. exact (@lem7200562 A (term75 R) (term164 A R)). Qed.
Lemma lem7200564 {A : Type'} (R : type1626) (f : A -> real) : (term165 A R f) = (term143 A R f).
Proof. exact (eq_refl (term165 A R f)). Qed.
Lemma lem7200565 (R : type1626) : (term77 R) = (term77 R).
Proof. exact (eq_refl (term77 R)). Qed.
Lemma lem7200566 {A : Type'} (R : type1626) (f : A -> real) : (term166 A R f) = (term144 A R f).
Proof. exact (MK_COMB (@lem7200565 R) (@lem7200564 A R f)). Qed.
Lemma lem7200567 {A : Type'} (R : type1626) : (term167 A R) = (term152 A R).
Proof. exact (fun_ext (fun f : A -> real => @lem7200566 A R f)). Qed.
Lemma lem7200568 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7200569 {A : Type'} (R : type1626) : (term162 A R) = (term160 A R).
Proof. exact (MK_COMB (@lem7200568 A) (@lem7200567 A R)). Qed.
Lemma lem7200570 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7200571 {A : Type'} (R : type1626) : (term168 A R) = (term169 A R).
Proof. exact (MK_COMB (@lem7200570) (@lem7200569 A R)). Qed.
Lemma lem7200572 {A : Type'} (R : type1626) (f : A -> real) : (term165 A R f) = (term143 A R f).
Proof. exact (eq_refl (term165 A R f)). Qed.
Lemma lem7200573 {A : Type'} (R : type1626) : (term170 A R) = (term164 A R).
Proof. exact (fun_ext (fun f : A -> real => @lem7200572 A R f)). Qed.
Lemma lem7200574 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7200575 {A : Type'} (R : type1626) : (term171 A R) = (term172 A R).
Proof. exact (MK_COMB (@lem7200574 A) (@lem7200573 A R)). Qed.
Lemma lem7200576 (R : type1626) : (term77 R) = (term77 R).
Proof. exact (eq_refl (term77 R)). Qed.
Lemma lem7200577 {A : Type'} (R : type1626) : (term163 A R) = (term173 A R).
Proof. exact (MK_COMB (@lem7200576 R) (@lem7200575 A R)). Qed.
Lemma lem7200578 {A : Type'} (R : type1626) : ((term162 A R) = (term163 A R)) = ((term160 A R) = (term173 A R)).
Proof. exact (MK_COMB (@lem7200571 A R) (@lem7200577 A R)). Qed.
Lemma lem7200579 {A : Type'} (R : type1626) : (term160 A R) = (term173 A R).
Proof. exact (EQ_MP (@lem7200578 A R) (@lem7200563 A R)). Qed.
Lemma lem7200704 (R : type1626) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7200705 {A : Type'} (R : type1626) : (term161 A R) = (term174 A R).
Proof. exact (MK_COMB (@lem7200704 R) (@lem7200579 A R)). Qed.
Lemma lem7200708 {A : Type'} (R : type1626) : (term149 A R) = (term174 A R).
Proof. exact (TRANS (@lem7200557 A R) (@lem7200705 A R)). Qed.
Lemma lem7200709 {A : Type'} (R : type1626) : (term148 A R) = (term174 A R).
Proof. exact (TRANS (@lem7200537 A R) (@lem7200708 A R)). Qed.
Lemma lem7200710 {A : Type'} : (term175 A) = (term176 A).
Proof. exact (fun_ext (fun R : type1626 => @lem7200709 A R)). Qed.
Lemma lem7200711 : (@all (real -> real -> Prop)) = (@all (real -> real -> Prop)).
Proof. exact (eq_refl (@all (real -> real -> Prop))). Qed.
Lemma lem7200712 {A : Type'} : (term177 A) = (term178 A).
Proof. exact (MK_COMB (@lem7200711) (@lem7200710 A)). Qed.
Lemma lem7200737 {A : Type'} : (term178 A) = (term177 A).
Proof. exact (SYM (@lem7200712 A)). Qed.
Lemma lem7200738 (R : type1626) (h1 : term23 R) : term23 R.
Proof. exact (h1). Qed.
Lemma lem7200739 (R : type1626) (h1 : term75 R) : term75 R.
Proof. exact (h1). Qed.
Lemma lem7200740 (R : type1626) : (term23 R) = ((term23 R) = True).
Proof. exact (@lem7 (term23 R)). Qed.
Lemma lem7200757 : (@neutral real real_add) = term179.
Proof. exact (EQ_MP (@lem7064171) (@lem7065437)). Qed.
Lemma lem7200758 (R : type1626) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7200759 (R : type1626) : (term180 R) = (term181 R).
Proof. exact (MK_COMB (@lem7200758 R) (@lem7200757)). Qed.
Lemma lem7200761 : (@neutral real real_add) = term179.
Proof. exact (EQ_MP (@lem7064171) (@lem7065437)). Qed.
Lemma lem7200762 (R : type1626) : (term182 R) = (term23 R).
Proof. exact (MK_COMB (@lem7200759 R) (@lem7200761)). Qed.
Lemma lem7200764 (R : type1626) (h1 : term23 R) : (term23 R) = True.
Proof. exact (EQ_MP (@lem7200740 R) (@lem7200738 R h1)). Qed.
Lemma lem7200765 (R : type1626) (h1 : term23 R) : (term182 R) = True.
Proof. exact (TRANS (@lem7200762 R) (@lem7200764 R h1)). Qed.
Lemma lem7200766 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7200767 (R : type1626) (h1 : term23 R) : (term183 R) = (and True).
Proof. exact (MK_COMB (@lem7200766) (@lem7200765 R h1)). Qed.
Lemma lem7200788 (R : type1626) : (term184 R) = (term184 R).
Proof. exact (eq_refl (term184 R)). Qed.
Lemma lem7200789 (R : type1626) (h1 : term23 R) : (term185 R) = (term186 R).
Proof. exact (MK_COMB (@lem7200767 R h1) (@lem7200788 R)). Qed.
Lemma lem7200791 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7200792 (R : type1626) : (term186 R) = (term184 R).
Proof. exact (@lem7200791 (term184 R)). Qed.
Lemma lem7200813 (R : type1626) (h1 : term23 R) : (term185 R) = (term184 R).
Proof. exact (TRANS (@lem7200789 R h1) (@lem7200792 R)). Qed.
Lemma lem7200814 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7200815 (R : type1626) (h1 : term23 R) : (term187 R) = (term188 R).
Proof. exact (MK_COMB (@lem7200814) (@lem7200813 R h1)). Qed.
Lemma lem7200839 {_131408 : Type'} : (@iterate real _131408 real_add) = (@sum _131408).
Proof. exact (EQ_MP (@lem7199903 _131408) (@lem7064112 _131408)). Qed.
Lemma lem7200840 {A : Type'} : (@iterate real A real_add) = (@sum A).
Proof. exact (@lem7200839 A). Qed.
Lemma lem7200841 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7200842 {A : Type'} (s : A -> Prop) : (@iterate real A real_add s) = (@sum A s).
Proof. exact (MK_COMB (@lem7200840 A) (@lem7200841 A s)). Qed.
Lemma lem7200843 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7200844 {A : Type'} (s : A -> Prop) (f : A -> real) : (@iterate real A real_add s f) = (@sum A s f).
Proof. exact (MK_COMB (@lem7200842 A s) (@lem7200843 A f)). Qed.
Lemma lem7200845 (R : type1626) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7200846 {A : Type'} (R : type1626) (s : A -> Prop) (f : A -> real) : (term189 A R s f) = (term190 A R s f).
Proof. exact (MK_COMB (@lem7200845 R) (@lem7200844 A s f)). Qed.
Lemma lem7200848 {_131408 : Type'} : (@iterate real _131408 real_add) = (@sum _131408).
Proof. exact (EQ_MP (@lem7199903 _131408) (@lem7064112 _131408)). Qed.
Lemma lem7200849 {A : Type'} : (@iterate real A real_add) = (@sum A).
Proof. exact (@lem7200848 A). Qed.
Lemma lem7200850 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7200851 {A : Type'} (s : A -> Prop) : (@iterate real A real_add s) = (@sum A s).
Proof. exact (MK_COMB (@lem7200849 A) (@lem7200850 A s)). Qed.
Lemma lem7200852 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7200853 {A : Type'} (s : A -> Prop) (g : A -> real) : (@iterate real A real_add s g) = (@sum A s g).
Proof. exact (MK_COMB (@lem7200851 A s) (@lem7200852 A g)). Qed.
Lemma lem7200854 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term191 A R f s g) = (term25 A R f s g).
Proof. exact (MK_COMB (@lem7200846 A R s f) (@lem7200853 A s g)). Qed.
Lemma lem7200855 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term192 A s R f g) = (term192 A s R f g).
Proof. exact (eq_refl (term192 A s R f g)). Qed.
Lemma lem7200856 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term193 A R f s g) = (term78 A R f s g).
Proof. exact (MK_COMB (@lem7200855 A s R f g) (@lem7200854 A R f s g)). Qed.
Lemma lem7200859 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term194 A R f g) = (term195 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7200856 A R f s g)). Qed.
Lemma lem7200860 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7200861 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term196 A R f g) = (term197 A R f g).
Proof. exact (MK_COMB (@lem7200860 A) (@lem7200859 A R f g)). Qed.
Lemma lem7200866 {A : Type'} (R : type1626) (f : A -> real) : (term198 A R f) = (term199 A R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7200861 A R f g)). Qed.
Lemma lem7200867 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7200868 {A : Type'} (R : type1626) (f : A -> real) : (term200 A R f) = (term201 A R f).
Proof. exact (MK_COMB (@lem7200867 A) (@lem7200866 A R f)). Qed.
Lemma lem7200873 {A : Type'} (R : type1626) : (term202 A R) = (term203 A R).
Proof. exact (fun_ext (fun f : A -> real => @lem7200868 A R f)). Qed.
Lemma lem7200874 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7200875 {A : Type'} (R : type1626) : (term204 A R) = (term205 A R).
Proof. exact (MK_COMB (@lem7200874 A) (@lem7200873 A R)). Qed.
Lemma lem7200880 {A : Type'} (R : type1626) (h1 : term23 R) : (term13 A R) = (term206 A R).
Proof. exact (MK_COMB (@lem7200815 R h1) (@lem7200875 A R)). Qed.
Lemma lem7200883 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7200884 {A : Type'} (R : type1626) (h1 : term23 R) : (term207 A R) = (term208 A R).
Proof. exact (MK_COMB (@lem7200883) (@lem7200880 A R h1)). Qed.
Lemma lem7200907 {A : Type'} (R : type1626) : (term172 A R) = (term172 A R).
Proof. exact (eq_refl (term172 A R)). Qed.
Lemma lem7200908 {A : Type'} (R : type1626) (h1 : term23 R) : (term209 A R) = (term210 A R).
Proof. exact (MK_COMB (@lem7200884 A R h1) (@lem7200907 A R)). Qed.
Lemma lem7200911 {A : Type'} (R : type1626) (h1 : term23 R) : (term210 A R) = (term209 A R).
Proof. exact (SYM (@lem7200908 A R h1)). Qed.
Lemma lem7200913 (p : Prop) : p = (term211 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7200914 {A : Type'} (R : type1626) : (term210 A R) = (term212 A R).
Proof. exact (@lem7200913 (term210 A R)). Qed.
Lemma lem7200915 {A : Type'} (R : type1626) : (term212 A R) = (term210 A R).
Proof. exact (SYM (@lem7200914 A R)). Qed.
Lemma lem7200916 {A : Type'} (R : type1626) (h1 : term213 A R) : term213 A R.
Proof. exact (h1). Qed.
Lemma lem7200919 {A : Type'} (R : type1626) (h1 : term214 A R) : term214 A R.
Proof. exact (h1). Qed.
Lemma lem7200920 {A : Type'} (R : type1626) : term215 A R.
Proof. exact (fun h0 : term214 A R => @lem7200919 A R h0). Qed.
Lemma lem7200921 {A : Type'} (R : type1626) (h1 : term215 A R) : term215 A R.
Proof. exact (h1). Qed.
Lemma lem7200922 {A : Type'} (R : type1626) (h1 : term214 A R) : term214 A R.
Proof. exact (h1). Qed.
Lemma lem7200923 {A : Type'} (R : type1626) (h1 : term215 A R) (h2 : term214 A R) : term214 A R.
Proof. exact (@lem7200921 A R h1 (@lem7200922 A R h2)). Qed.
Lemma lem7200924 {A : Type'} (R : type1626) (h1 : term214 A R) : term216 A R.
Proof. exact (fun h0 : term215 A R => @lem7200923 A R h0 h1). Qed.
Lemma lem7200925 {A : Type'} (R : type1626) (h1 : term215 A R) : term215 A R.
Proof. exact (h1). Qed.
Lemma lem7200926 {A : Type'} (R : type1626) (h1 : term215 A R) (h2 : term214 A R) : term214 A R.
Proof. exact (@lem7200924 A R h2 (@lem7200925 A R h1)). Qed.
Lemma lem7200927 {A : Type'} (R : type1626) (h1 : term215 A R) : term215 A R.
Proof. exact (fun h0 : term214 A R => @lem7200926 A R h1 h0). Qed.
Lemma lem7200928 {A : Type'} (R : type1626) : term217 A R.
Proof. exact (fun h0 : term215 A R => @lem7200927 A R h0). Qed.
Lemma lem7200931 {A : Type'} (R : type1626) : term215 A R.
Proof. exact (@lem7200928 A R (@lem7200920 A R)). Qed.
Lemma lem7200932 {A : Type'} (R : type1626) : term215 A R.
Proof. exact (@lem7200931 A R). Qed.
Lemma lem7200962 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7200963 {A : Type'} (R : type1626) : (term212 A R) = (term218 A R).
Proof. exact (@lem7200962 (term213 A R)). Qed.
Lemma lem7200965 (t : Prop) : (term219 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7200966 {A : Type'} (R : type1626) : (term218 A R) = (term210 A R).
Proof. exact (@lem7200965 (term210 A R)). Qed.
Lemma lem7200969 {A : Type'} (R : type1626) : (term212 A R) = (term210 A R).
Proof. exact (TRANS (@lem7200963 A R) (@lem7200966 A R)). Qed.
Lemma lem7201036 (R : type1626) : (term77 R) = (term77 R).
Proof. exact (eq_refl (term77 R)). Qed.
Lemma lem7201037 {A : Type'} (R : type1626) : (term220 A R) = (term221 A R).
Proof. exact (MK_COMB (@lem7201036 R) (@lem7200969 A R)). Qed.
Lemma lem7201040 (R : type1626) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7201041 {A : Type'} (R : type1626) : (term214 A R) = (term222 A R).
Proof. exact (MK_COMB (@lem7201040 R) (@lem7201037 A R)). Qed.
Lemma lem7201044 {A : Type'} : (term223 A) = (term224 A).
Proof. exact (fun_ext (fun R : type1626 => @lem7201041 A R)). Qed.
Lemma lem7201045 : (@all (real -> real -> Prop)) = (@all (real -> real -> Prop)).
Proof. exact (eq_refl (@all (real -> real -> Prop))). Qed.
Lemma lem7201054 {A : Type'} : (term225 A) = (term226 A).
Proof. exact (MK_COMB (@lem7201045) (@lem7201044 A)). Qed.
Lemma lem7201055 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7201060 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term227 A s R f g x) = (term227 A s R f g x).
Proof. exact (eq_refl (term227 A s R f g x)). Qed.
Lemma lem7201061 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term228 A s R f g) = (term228 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7201060 A s R f g x)). Qed.
Lemma lem7201062 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7201063 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term80 A s R f g) = (term80 A s R f g).
Proof. exact (MK_COMB (@lem7201062 A) (@lem7201061 A s R f g)). Qed.
Lemma lem7201064 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7201065 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term229 A s R f g) = (term229 A s R f g).
Proof. exact (MK_COMB (@lem7201064) (@lem7201063 A s R f g)). Qed.
Lemma lem7201066 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term230 A R f s g) = (term230 A R f s g).
Proof. exact (MK_COMB (@lem7201065 A s R f g) (@lem7201055 A R f s g)). Qed.
Lemma lem7201069 {A : Type'} (s : A -> Prop) : (term231 A s) = (term231 A s).
Proof. exact (eq_refl (term231 A s)). Qed.
Lemma lem7201070 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term79 A R f s g) = (term79 A R f s g).
Proof. exact (MK_COMB (@lem7201069 A s) (@lem7201066 A R f s g)). Qed.
Lemma lem7201071 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term104 A R f g) = (term104 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7201070 A R f s g)). Qed.
Lemma lem7201072 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7201073 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term112 A R f g) = (term112 A R f g).
Proof. exact (MK_COMB (@lem7201072 A) (@lem7201071 A R f g)). Qed.
Lemma lem7201074 {A : Type'} (R : type1626) (f : A -> real) : (term135 A R f) = (term135 A R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7201073 A R f g)). Qed.
Lemma lem7201075 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7201076 {A : Type'} (R : type1626) (f : A -> real) : (term143 A R f) = (term143 A R f).
Proof. exact (MK_COMB (@lem7201075 A) (@lem7201074 A R f)). Qed.
Lemma lem7201077 {A : Type'} (R : type1626) : (term164 A R) = (term164 A R).
Proof. exact (fun_ext (fun f : A -> real => @lem7201076 A R f)). Qed.
Lemma lem7201078 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7201079 {A : Type'} (R : type1626) : (term172 A R) = (term172 A R).
Proof. exact (MK_COMB (@lem7201078 A) (@lem7201077 A R)). Qed.
Lemma lem7201080 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7201085 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term227 A s R f g x) = (term227 A s R f g x).
Proof. exact (eq_refl (term227 A s R f g x)). Qed.
Lemma lem7201086 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term228 A s R f g) = (term228 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7201085 A s R f g x)). Qed.
Lemma lem7201087 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7201088 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term80 A s R f g) = (term80 A s R f g).
Proof. exact (MK_COMB (@lem7201087 A) (@lem7201086 A s R f g)). Qed.
Lemma lem7201091 {A : Type'} (s : A -> Prop) : (term232 A s) = (term232 A s).
Proof. exact (eq_refl (term232 A s)). Qed.
Lemma lem7201092 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term29 A s R f g) = (term29 A s R f g).
Proof. exact (MK_COMB (@lem7201091 A s) (@lem7201088 A s R f g)). Qed.
Lemma lem7201093 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7201094 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term192 A s R f g) = (term192 A s R f g).
Proof. exact (MK_COMB (@lem7201093) (@lem7201092 A s R f g)). Qed.
Lemma lem7201095 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term78 A R f s g) = (term78 A R f s g).
Proof. exact (MK_COMB (@lem7201094 A s R f g) (@lem7201080 A R f s g)). Qed.
Lemma lem7201096 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term195 A R f g) = (term195 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7201095 A R f s g)). Qed.
Lemma lem7201097 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7201098 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term197 A R f g) = (term197 A R f g).
Proof. exact (MK_COMB (@lem7201097 A) (@lem7201096 A R f g)). Qed.
Lemma lem7201099 {A : Type'} (R : type1626) (f : A -> real) : (term199 A R f) = (term199 A R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7201098 A R f g)). Qed.
Lemma lem7201100 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7201101 {A : Type'} (R : type1626) (f : A -> real) : (term201 A R f) = (term201 A R f).
Proof. exact (MK_COMB (@lem7201100 A) (@lem7201099 A R f)). Qed.
Lemma lem7201102 {A : Type'} (R : type1626) : (term203 A R) = (term203 A R).
Proof. exact (fun_ext (fun f : A -> real => @lem7201101 A R f)). Qed.
Lemma lem7201103 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7201104 {A : Type'} (R : type1626) : (term205 A R) = (term205 A R).
Proof. exact (MK_COMB (@lem7201103 A) (@lem7201102 A R)). Qed.
Lemma lem7201113 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term30 R x1 y1 x2 y2) = (term30 R x1 y1 x2 y2).
Proof. exact (eq_refl (term30 R x1 y1 x2 y2)). Qed.
Lemma lem7201114 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term33 R x1 y1 x2) = (term33 R x1 y1 x2).
Proof. exact (fun_ext (fun y2 : real => @lem7201113 R x1 y1 x2 y2)). Qed.
Lemma lem7201115 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7201116 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term35 R x1 y1 x2) = (term35 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7201115) (@lem7201114 R x1 y1 x2)). Qed.
Lemma lem7201117 (R : type1626) (x1 : real) (y1 : real) : (term233 R x1 y1) = (term233 R x1 y1).
Proof. exact (fun_ext (fun x2 : real => @lem7201116 R x1 y1 x2)). Qed.
Lemma lem7201118 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7201119 (R : type1626) (x1 : real) (y1 : real) : (term234 R x1 y1) = (term234 R x1 y1).
Proof. exact (MK_COMB (@lem7201118) (@lem7201117 R x1 y1)). Qed.
Lemma lem7201120 (R : type1626) (x1 : real) : (term235 R x1) = (term235 R x1).
Proof. exact (fun_ext (fun y1 : real => @lem7201119 R x1 y1)). Qed.
Lemma lem7201121 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7201122 (R : type1626) (x1 : real) : (term236 R x1) = (term236 R x1).
Proof. exact (MK_COMB (@lem7201121) (@lem7201120 R x1)). Qed.
Lemma lem7201123 (R : type1626) : (term237 R) = (term237 R).
Proof. exact (fun_ext (fun x1 : real => @lem7201122 R x1)). Qed.
Lemma lem7201124 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7201125 (R : type1626) : (term184 R) = (term184 R).
Proof. exact (MK_COMB (@lem7201124) (@lem7201123 R)). Qed.
Lemma lem7201126 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7201127 (R : type1626) : (term188 R) = (term188 R).
Proof. exact (MK_COMB (@lem7201126) (@lem7201125 R)). Qed.
Lemma lem7201128 {A : Type'} (R : type1626) : (term206 A R) = (term206 A R).
Proof. exact (MK_COMB (@lem7201127 R) (@lem7201104 A R)). Qed.
Lemma lem7201129 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7201130 {A : Type'} (R : type1626) : (term208 A R) = (term208 A R).
Proof. exact (MK_COMB (@lem7201129) (@lem7201128 A R)). Qed.
Lemma lem7201131 {A : Type'} (R : type1626) : (term210 A R) = (term210 A R).
Proof. exact (MK_COMB (@lem7201130 A R) (@lem7201079 A R)). Qed.
Lemma lem7201136 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term43 R m m' n n') = (term43 R m m' n n').
Proof. exact (eq_refl (term43 R m m' n n')). Qed.
Lemma lem7201137 (R : type1626) (m : real) (m' : real) (n : real) : (term41 R m m' n) = (term41 R m m' n).
Proof. exact (fun_ext (fun n' : real => @lem7201136 R m m' n n')). Qed.
Lemma lem7201138 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7201139 (R : type1626) (m : real) (m' : real) (n : real) : (term51 R m m' n) = (term51 R m m' n).
Proof. exact (MK_COMB (@lem7201138) (@lem7201137 R m m' n)). Qed.
Lemma lem7201140 (R : type1626) (m : real) (n : real) : (term59 R m n) = (term59 R m n).
Proof. exact (fun_ext (fun m' : real => @lem7201139 R m m' n)). Qed.
Lemma lem7201141 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7201142 (R : type1626) (m : real) (n : real) : (term67 R m n) = (term67 R m n).
Proof. exact (MK_COMB (@lem7201141) (@lem7201140 R m n)). Qed.
Lemma lem7201145 (R : type1626) (m : real) (n : real) : (term44 R m n) = (term44 R m n).
Proof. exact (eq_refl (term44 R m n)). Qed.
Lemma lem7201146 (R : type1626) (m : real) (n : real) : (term68 R m n) = (term68 R m n).
Proof. exact (MK_COMB (@lem7201145 R m n) (@lem7201142 R m n)). Qed.
Lemma lem7201147 (R : type1626) (m : real) : (term70 R m) = (term70 R m).
Proof. exact (fun_ext (fun n : real => @lem7201146 R m n)). Qed.
Lemma lem7201148 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7201149 (R : type1626) (m : real) : (term72 R m) = (term72 R m).
Proof. exact (MK_COMB (@lem7201148) (@lem7201147 R m)). Qed.
Lemma lem7201150 (R : type1626) : (term74 R) = (term74 R).
Proof. exact (fun_ext (fun m : real => @lem7201149 R m)). Qed.
Lemma lem7201151 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7201152 (R : type1626) : (term75 R) = (term75 R).
Proof. exact (MK_COMB (@lem7201151) (@lem7201150 R)). Qed.
Lemma lem7201153 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7201154 (R : type1626) : (term77 R) = (term77 R).
Proof. exact (MK_COMB (@lem7201153) (@lem7201152 R)). Qed.
Lemma lem7201155 {A : Type'} (R : type1626) : (term221 A R) = (term221 A R).
Proof. exact (MK_COMB (@lem7201154 R) (@lem7201131 A R)). Qed.
Lemma lem7201158 (R : type1626) : (term82 R) = (term82 R).
Proof. exact (eq_refl (term82 R)). Qed.
Lemma lem7201159 {A : Type'} (R : type1626) : (term222 A R) = (term222 A R).
Proof. exact (MK_COMB (@lem7201158 R) (@lem7201155 A R)). Qed.
Lemma lem7201160 {A : Type'} : (term224 A) = (term224 A).
Proof. exact (fun_ext (fun R : type1626 => @lem7201159 A R)). Qed.
Lemma lem7201161 : (@all (real -> real -> Prop)) = (@all (real -> real -> Prop)).
Proof. exact (eq_refl (@all (real -> real -> Prop))). Qed.
Lemma lem7201162 {A : Type'} : (term226 A) = (term226 A).
Proof. exact (MK_COMB (@lem7201161) (@lem7201160 A)). Qed.
Lemma lem7201295 {A : Type'} : (term225 A) = (term226 A).
Proof. exact (TRANS (@lem7201054 A) (@lem7201162 A)). Qed.
Lemma lem7201296 {A : Type'} : (term226 A) = (term225 A).
Proof. exact (SYM (@lem7201295 A)). Qed.
Lemma lem7201298 (R : type1626) (h1 : term75 R) : term75 R.
Proof. exact (h1). Qed.
Lemma lem7201299 {A : Type'} (R : type1626) (h1 : term206 A R) : term206 A R.
Proof. exact (h1). Qed.
Lemma lem7201301 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (h1 : term80 A s R f g) : term80 A s R f g.
Proof. exact (h1). Qed.
Lemma lem7201303 (p : Prop) : p = (term211 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7201304 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term238 A R f s g).
Proof. exact (@lem7201303 (term25 A R f s g)). Qed.
Lemma lem7201305 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term238 A R f s g) = (term25 A R f s g).
Proof. exact (SYM (@lem7201304 A R f s g)). Qed.
Lemma lem7201306 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term239 A R f s g) : term239 A R f s g.
Proof. exact (h1). Qed.
Lemma lem7201320 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term43 R m m' n n') = (term240 R m m' n n').
Proof. exact (@lem17265 (R m' n') (term32 R m m' n n')). Qed.
Lemma lem7201321 (R : type1626) (m : real) (m' : real) (n : real) : (term41 R m m' n) = (term241 R m m' n).
Proof. exact (fun_ext (fun n' : real => @lem7201320 R m m' n n')). Qed.
Lemma lem7201322 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7201323 (R : type1626) (m : real) (m' : real) (n : real) : (term51 R m m' n) = (term242 R m m' n).
Proof. exact (MK_COMB (@lem7201322) (@lem7201321 R m m' n)). Qed.
Lemma lem7201324 (R : type1626) (m : real) (n : real) : (term59 R m n) = (term243 R m n).
Proof. exact (fun_ext (fun m' : real => @lem7201323 R m m' n)). Qed.
Lemma lem7201325 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7201326 (R : type1626) (m : real) (n : real) : (term67 R m n) = (term244 R m n).
Proof. exact (MK_COMB (@lem7201325) (@lem7201324 R m n)). Qed.
Lemma lem7201328 (R : type1626) (m : real) (n : real) : (term245 R m n) = (term245 R m n).
Proof. exact (eq_refl (term245 R m n)). Qed.
Lemma lem7201329 (R : type1626) (m : real) (n : real) : (term246 R m n) = (term247 R m n).
Proof. exact (MK_COMB (@lem7201328 R m n) (@lem7201326 R m n)). Qed.
Lemma lem7201330 (R : type1626) (m : real) (n : real) : (term68 R m n) = (term246 R m n).
Proof. exact (@lem17265 (R m n) (term67 R m n)). Qed.
Lemma lem7201331 (R : type1626) (m : real) (n : real) : (term68 R m n) = (term247 R m n).
Proof. exact (TRANS (@lem7201330 R m n) (@lem7201329 R m n)). Qed.
Lemma lem7201332 (R : type1626) (m : real) : (term70 R m) = (term248 R m).
Proof. exact (fun_ext (fun n : real => @lem7201331 R m n)). Qed.
Lemma lem7201333 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7201334 (R : type1626) (m : real) : (term72 R m) = (term249 R m).
Proof. exact (MK_COMB (@lem7201333) (@lem7201332 R m)). Qed.
Lemma lem7201335 (R : type1626) : (term74 R) = (term250 R).
Proof. exact (fun_ext (fun m : real => @lem7201334 R m)). Qed.
Lemma lem7201336 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7201445 (R : type1626) : (term75 R) = (term251 R).
Proof. exact (MK_COMB (@lem7201336) (@lem7201335 R)). Qed.
Lemma lem7201446 (R : type1626) (h1 : term75 R) : term251 R.
Proof. exact (EQ_MP (@lem7201445 R) (@lem7201298 R h1)). Qed.
Lemma lem7201457 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term252 R x1 y1 x2 y2) = (term253 R x1 y1 x2 y2).
Proof. exact (@lem17362 (term254 x1 x2 R y1 y2) (term32 R x1 y1 x2 y2)). Qed.
Lemma lem7201458 (P : real -> Prop) : (term255 P) = (term256 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7201459 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term257 R x1 y1 x2) = (term258 R x1 y1 x2).
Proof. exact (@lem7201458 (term33 R x1 y1 x2)). Qed.
Lemma lem7201460 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term259 R x1 y1 x2 y2) = (term30 R x1 y1 x2 y2).
Proof. exact (eq_refl (term259 R x1 y1 x2 y2)). Qed.
Lemma lem7201461 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7201462 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term260 R x1 y1 x2 y2) = (term252 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7201461) (@lem7201460 R x1 y1 x2 y2)). Qed.
Lemma lem7201463 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term260 R x1 y1 x2 y2) = (term253 R x1 y1 x2 y2).
Proof. exact (TRANS (@lem7201462 R x1 y1 x2 y2) (@lem7201457 R x1 y1 x2 y2)). Qed.
Lemma lem7201464 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term261 R x1 y1 x2) = (term262 R x1 y1 x2).
Proof. exact (fun_ext (fun y2 : real => @lem7201463 R x1 y1 x2 y2)). Qed.
Lemma lem7201465 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7201466 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term258 R x1 y1 x2) = (term263 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7201465) (@lem7201464 R x1 y1 x2)). Qed.
Lemma lem7201467 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term257 R x1 y1 x2) = (term263 R x1 y1 x2).
Proof. exact (TRANS (@lem7201459 R x1 y1 x2) (@lem7201466 R x1 y1 x2)). Qed.
Lemma lem7201468 (P : real -> Prop) : (term255 P) = (term256 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7201469 (R : type1626) (x1 : real) (y1 : real) : (term264 R x1 y1) = (term265 R x1 y1).
Proof. exact (@lem7201468 (term233 R x1 y1)). Qed.
Lemma lem7201470 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term266 R x1 y1 x2) = (term35 R x1 y1 x2).
Proof. exact (eq_refl (term266 R x1 y1 x2)). Qed.
Lemma lem7201471 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7201472 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term267 R x1 y1 x2) = (term257 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7201471) (@lem7201470 R x1 y1 x2)). Qed.
Lemma lem7201473 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term267 R x1 y1 x2) = (term263 R x1 y1 x2).
Proof. exact (TRANS (@lem7201472 R x1 y1 x2) (@lem7201467 R x1 y1 x2)). Qed.
Lemma lem7201474 (R : type1626) (x1 : real) (y1 : real) : (term268 R x1 y1) = (term269 R x1 y1).
Proof. exact (fun_ext (fun x2 : real => @lem7201473 R x1 y1 x2)). Qed.
Lemma lem7201475 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7201476 (R : type1626) (x1 : real) (y1 : real) : (term265 R x1 y1) = (term270 R x1 y1).
Proof. exact (MK_COMB (@lem7201475) (@lem7201474 R x1 y1)). Qed.
Lemma lem7201477 (R : type1626) (x1 : real) (y1 : real) : (term264 R x1 y1) = (term270 R x1 y1).
Proof. exact (TRANS (@lem7201469 R x1 y1) (@lem7201476 R x1 y1)). Qed.
Lemma lem7201478 (P : real -> Prop) : (term255 P) = (term256 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7201479 (R : type1626) (x1 : real) : (term271 R x1) = (term272 R x1).
Proof. exact (@lem7201478 (term235 R x1)). Qed.
Lemma lem7201480 (R : type1626) (x1 : real) (y1 : real) : (term273 R x1 y1) = (term234 R x1 y1).
Proof. exact (eq_refl (term273 R x1 y1)). Qed.
Lemma lem7201481 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7201482 (R : type1626) (x1 : real) (y1 : real) : (term274 R x1 y1) = (term264 R x1 y1).
Proof. exact (MK_COMB (@lem7201481) (@lem7201480 R x1 y1)). Qed.
Lemma lem7201483 (R : type1626) (x1 : real) (y1 : real) : (term274 R x1 y1) = (term270 R x1 y1).
Proof. exact (TRANS (@lem7201482 R x1 y1) (@lem7201477 R x1 y1)). Qed.
Lemma lem7201484 (R : type1626) (x1 : real) : (term275 R x1) = (term276 R x1).
Proof. exact (fun_ext (fun y1 : real => @lem7201483 R x1 y1)). Qed.
Lemma lem7201485 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7201486 (R : type1626) (x1 : real) : (term272 R x1) = (term277 R x1).
Proof. exact (MK_COMB (@lem7201485) (@lem7201484 R x1)). Qed.
Lemma lem7201487 (R : type1626) (x1 : real) : (term271 R x1) = (term277 R x1).
Proof. exact (TRANS (@lem7201479 R x1) (@lem7201486 R x1)). Qed.
Lemma lem7201488 (P : real -> Prop) : (term255 P) = (term256 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7201489 (R : type1626) : (term278 R) = (term279 R).
Proof. exact (@lem7201488 (term237 R)). Qed.
Lemma lem7201490 (R : type1626) (x1 : real) : (term280 R x1) = (term236 R x1).
Proof. exact (eq_refl (term280 R x1)). Qed.
Lemma lem7201491 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7201492 (R : type1626) (x1 : real) : (term281 R x1) = (term271 R x1).
Proof. exact (MK_COMB (@lem7201491) (@lem7201490 R x1)). Qed.
Lemma lem7201493 (R : type1626) (x1 : real) : (term281 R x1) = (term277 R x1).
Proof. exact (TRANS (@lem7201492 R x1) (@lem7201487 R x1)). Qed.
Lemma lem7201494 (R : type1626) : (term282 R) = (term283 R).
Proof. exact (fun_ext (fun x1 : real => @lem7201493 R x1)). Qed.
Lemma lem7201495 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7201496 (R : type1626) : (term279 R) = (term284 R).
Proof. exact (MK_COMB (@lem7201495) (@lem7201494 R)). Qed.
Lemma lem7201497 (R : type1626) : (term278 R) = (term284 R).
Proof. exact (TRANS (@lem7201489 R) (@lem7201496 R)). Qed.
Lemma lem7201505 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term285 A s R f g x) = (term286 A s R f g x).
Proof. exact (@lem17362 (@IN A x s) (term287 A R f g x)). Qed.
Lemma lem7201506 {A : Type'} (P : A -> Prop) : (term288 A P) = (term289 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7201507 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term290 A s R f g) = (term291 A s R f g).
Proof. exact (@lem7201506 A (term228 A s R f g)). Qed.
Lemma lem7201508 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term292 A s R f g x) = (term227 A s R f g x).
Proof. exact (eq_refl (term292 A s R f g x)). Qed.
Lemma lem7201509 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7201510 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term293 A s R f g x) = (term285 A s R f g x).
Proof. exact (MK_COMB (@lem7201509) (@lem7201508 A s R f g x)). Qed.
Lemma lem7201511 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term293 A s R f g x) = (term286 A s R f g x).
Proof. exact (TRANS (@lem7201510 A s R f g x) (@lem7201505 A s R f g x)). Qed.
Lemma lem7201512 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term294 A s R f g) = (term295 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7201511 A s R f g x)). Qed.
Lemma lem7201513 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7201514 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term291 A s R f g) = (term296 A s R f g).
Proof. exact (MK_COMB (@lem7201513 A) (@lem7201512 A s R f g)). Qed.
Lemma lem7201515 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term290 A s R f g) = (term296 A s R f g).
Proof. exact (TRANS (@lem7201507 A s R f g) (@lem7201514 A s R f g)). Qed.
Lemma lem7201517 {A : Type'} (s : A -> Prop) : (term297 A s) = (term297 A s).
Proof. exact (eq_refl (term297 A s)). Qed.
Lemma lem7201518 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term298 A s R f g) = (term299 A s R f g).
Proof. exact (MK_COMB (@lem7201517 A s) (@lem7201515 A s R f g)). Qed.
Lemma lem7201519 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term300 A s R f g) = (term298 A s R f g).
Proof. exact (@lem17045 (@FINITE A s) (term80 A s R f g)). Qed.
Lemma lem7201520 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term300 A s R f g) = (term299 A s R f g).
Proof. exact (TRANS (@lem7201519 A s R f g) (@lem7201518 A s R f g)). Qed.
Lemma lem7201521 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7201522 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7201523 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term301 A s R f g) = (term302 A s R f g).
Proof. exact (MK_COMB (@lem7201522) (@lem7201520 A s R f g)). Qed.
Lemma lem7201524 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term303 A R f s g) = (term304 A R f s g).
Proof. exact (MK_COMB (@lem7201523 A s R f g) (@lem7201521 A R f s g)). Qed.
Lemma lem7201525 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term78 A R f s g) = (term303 A R f s g).
Proof. exact (@lem17265 (term29 A s R f g) (term25 A R f s g)). Qed.
Lemma lem7201526 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term78 A R f s g) = (term304 A R f s g).
Proof. exact (TRANS (@lem7201525 A R f s g) (@lem7201524 A R f s g)). Qed.
Lemma lem7201527 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term195 A R f g) = (term305 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7201526 A R f s g)). Qed.
Lemma lem7201528 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7201529 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term197 A R f g) = (term306 A R f g).
Proof. exact (MK_COMB (@lem7201528 A) (@lem7201527 A R f g)). Qed.
Lemma lem7201530 {A : Type'} (R : type1626) (f : A -> real) : (term199 A R f) = (term307 A R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7201529 A R f g)). Qed.
Lemma lem7201531 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7201532 {A : Type'} (R : type1626) (f : A -> real) : (term201 A R f) = (term308 A R f).
Proof. exact (MK_COMB (@lem7201531 A) (@lem7201530 A R f)). Qed.
Lemma lem7201533 {A : Type'} (R : type1626) : (term203 A R) = (term309 A R).
Proof. exact (fun_ext (fun f : A -> real => @lem7201532 A R f)). Qed.
Lemma lem7201534 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7201535 {A : Type'} (R : type1626) : (term205 A R) = (term310 A R).
Proof. exact (MK_COMB (@lem7201534 A) (@lem7201533 A R)). Qed.
Lemma lem7201536 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7201537 (R : type1626) : (term311 R) = (term312 R).
Proof. exact (MK_COMB (@lem7201536) (@lem7201497 R)). Qed.
Lemma lem7201538 {A : Type'} (R : type1626) : (term313 A R) = (term314 A R).
Proof. exact (MK_COMB (@lem7201537 R) (@lem7201535 A R)). Qed.
Lemma lem7201539 {A : Type'} (R : type1626) : (term206 A R) = (term313 A R).
Proof. exact (@lem17265 (term184 R) (term205 A R)). Qed.
Lemma lem7201540 {A : Type'} (R : type1626) : (term206 A R) = (term314 A R).
Proof. exact (TRANS (@lem7201539 A R) (@lem7201538 A R)). Qed.
Lemma lem7201707 {A : Type'} (P : Prop) (Q : A -> Prop) : (term315 A P Q) = (term316 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7201708 {A : Type'} (P : Prop) (Q : A -> Prop) : (term315 A P Q) = (term316 A P Q).
Proof. exact (@lem7201707 A P Q). Qed.
Lemma lem7201709 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term317 A s R f g) = (term318 A s R f g).
Proof. exact (@lem7201708 A (term319 A s) (term295 A s R f g)). Qed.
Lemma lem7201710 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term320 A s R f g x) = (term286 A s R f g x).
Proof. exact (eq_refl (term320 A s R f g x)). Qed.
Lemma lem7201711 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term321 A s R f g) = (term295 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7201710 A s R f g x)). Qed.
Lemma lem7201712 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7201713 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term322 A s R f g) = (term296 A s R f g).
Proof. exact (MK_COMB (@lem7201712 A) (@lem7201711 A s R f g)). Qed.
Lemma lem7201714 {A : Type'} (s : A -> Prop) : (term297 A s) = (term297 A s).
Proof. exact (eq_refl (term297 A s)). Qed.
Lemma lem7201715 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term317 A s R f g) = (term299 A s R f g).
Proof. exact (MK_COMB (@lem7201714 A s) (@lem7201713 A s R f g)). Qed.
Lemma lem7201716 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7201717 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term323 A s R f g) = (term324 A s R f g).
Proof. exact (MK_COMB (@lem7201716) (@lem7201715 A s R f g)). Qed.
Lemma lem7201718 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term320 A s R f g x) = (term286 A s R f g x).
Proof. exact (eq_refl (term320 A s R f g x)). Qed.
Lemma lem7201719 {A : Type'} (s : A -> Prop) : (term297 A s) = (term297 A s).
Proof. exact (eq_refl (term297 A s)). Qed.
Lemma lem7201720 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term325 A s R f g x) = (term326 A s R f g x).
Proof. exact (MK_COMB (@lem7201719 A s) (@lem7201718 A s R f g x)). Qed.
Lemma lem7201721 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term327 A s R f g) = (term328 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7201720 A s R f g x)). Qed.
Lemma lem7201722 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7201723 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term318 A s R f g) = (term329 A s R f g).
Proof. exact (MK_COMB (@lem7201722 A) (@lem7201721 A s R f g)). Qed.
Lemma lem7201724 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : ((term317 A s R f g) = (term318 A s R f g)) = ((term299 A s R f g) = (term329 A s R f g)).
Proof. exact (MK_COMB (@lem7201717 A s R f g) (@lem7201723 A s R f g)). Qed.
Lemma lem7201725 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term299 A s R f g) = (term329 A s R f g).
Proof. exact (EQ_MP (@lem7201724 A s R f g) (@lem7201709 A s R f g)). Qed.
Lemma lem7201726 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7201727 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term302 A s R f g) = (term330 A s R f g).
Proof. exact (MK_COMB (@lem7201726) (@lem7201725 A s R f g)). Qed.
Lemma lem7201728 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7201729 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term304 A R f s g) = (term331 A R f s g).
Proof. exact (MK_COMB (@lem7201727 A s R f g) (@lem7201728 A R f s g)). Qed.
Lemma lem7201731 {A : Type'} (P : A -> Prop) (Q : Prop) : (term332 A P Q) = (term333 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7201732 {A : Type'} (P : A -> Prop) (Q : Prop) : (term332 A P Q) = (term333 A P Q).
Proof. exact (@lem7201731 A P Q). Qed.
Lemma lem7201733 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term334 A R f s g) = (term335 A R f s g).
Proof. exact (@lem7201732 A (term328 A s R f g) (term25 A R f s g)). Qed.
Lemma lem7201734 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term336 A s R f g x) = (term326 A s R f g x).
Proof. exact (eq_refl (term336 A s R f g x)). Qed.
Lemma lem7201735 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term337 A s R f g) = (term328 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7201734 A s R f g x)). Qed.
Lemma lem7201736 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7201737 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term338 A s R f g) = (term329 A s R f g).
Proof. exact (MK_COMB (@lem7201736 A) (@lem7201735 A s R f g)). Qed.
Lemma lem7201738 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7201739 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term339 A s R f g) = (term330 A s R f g).
Proof. exact (MK_COMB (@lem7201738) (@lem7201737 A s R f g)). Qed.
Lemma lem7201740 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7201741 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term334 A R f s g) = (term331 A R f s g).
Proof. exact (MK_COMB (@lem7201739 A s R f g) (@lem7201740 A R f s g)). Qed.
Lemma lem7201742 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7201743 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term340 A R f s g) = (term341 A R f s g).
Proof. exact (MK_COMB (@lem7201742) (@lem7201741 A R f s g)). Qed.
Lemma lem7201744 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term336 A s R f g x) = (term326 A s R f g x).
Proof. exact (eq_refl (term336 A s R f g x)). Qed.
Lemma lem7201745 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7201746 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term342 A s R f g x) = (term343 A s R f g x).
Proof. exact (MK_COMB (@lem7201745) (@lem7201744 A s R f g x)). Qed.
Lemma lem7201747 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term25 A R f s g).
Proof. exact (eq_refl (term25 A R f s g)). Qed.
Lemma lem7201748 {A : Type'} (x : A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term344 A x R f s g) = (term345 A x R f s g).
Proof. exact (MK_COMB (@lem7201746 A s R f g x) (@lem7201747 A R f s g)). Qed.
Lemma lem7201749 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term346 A R f s g) = (term347 A R f s g).
Proof. exact (fun_ext (fun x : A => @lem7201748 A x R f s g)). Qed.
Lemma lem7201750 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7201751 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term335 A R f s g) = (term348 A R f s g).
Proof. exact (MK_COMB (@lem7201750 A) (@lem7201749 A R f s g)). Qed.
Lemma lem7201752 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : ((term334 A R f s g) = (term335 A R f s g)) = ((term331 A R f s g) = (term348 A R f s g)).
Proof. exact (MK_COMB (@lem7201743 A R f s g) (@lem7201751 A R f s g)). Qed.
Lemma lem7201753 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term331 A R f s g) = (term348 A R f s g).
Proof. exact (EQ_MP (@lem7201752 A R f s g) (@lem7201733 A R f s g)). Qed.
Lemma lem7201754 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term304 A R f s g) = (term348 A R f s g).
Proof. exact (TRANS (@lem7201729 A R f s g) (@lem7201753 A R f s g)). Qed.
Lemma lem7201755 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term305 A R f g) = (term349 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7201754 A R f s g)). Qed.
Lemma lem7201756 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7201757 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term306 A R f g) = (term350 A R f g).
Proof. exact (MK_COMB (@lem7201756 A) (@lem7201755 A R f g)). Qed.
Lemma lem7201759 {A B : Type'} (P : type1413 A B) : (term351 A B P) = (term352 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7201760 {A : Type'} (P : type672 A) : (term353 A P) = (term354 A P).
Proof. exact (@lem7201759 (A -> Prop) A P). Qed.
Lemma lem7201761 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term355 A R f g) = (term356 A R f g).
Proof. exact (@lem7201760 A (term357 A R f g)). Qed.
Lemma lem7201762 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term358 A R f g s) = (term347 A R f s g).
Proof. exact (eq_refl (term358 A R f g s)). Qed.
Lemma lem7201763 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7201764 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (x : A) : (term359 A R f g s x) = (term360 A R f s g x).
Proof. exact (MK_COMB (@lem7201762 A R f s g) (@lem7201763 A x)). Qed.
Lemma lem7201765 {A : Type'} (x : A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term360 A R f s g x) = (term345 A x R f s g).
Proof. exact (eq_refl (term360 A R f s g x)). Qed.
Lemma lem7201766 {A : Type'} (x : A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term359 A R f g s x) = (term345 A x R f s g).
Proof. exact (TRANS (@lem7201764 A R f s g x) (@lem7201765 A x R f s g)). Qed.
Lemma lem7201767 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term361 A R f g s) = (term347 A R f s g).
Proof. exact (fun_ext (fun x : A => @lem7201766 A x R f s g)). Qed.
Lemma lem7201768 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7201769 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term362 A R f g s) = (term348 A R f s g).
Proof. exact (MK_COMB (@lem7201768 A) (@lem7201767 A R f s g)). Qed.
Lemma lem7201770 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term363 A R f g) = (term349 A R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7201769 A R f s g)). Qed.
Lemma lem7201771 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7201772 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term355 A R f g) = (term350 A R f g).
Proof. exact (MK_COMB (@lem7201771 A) (@lem7201770 A R f g)). Qed.
Lemma lem7201773 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7201774 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term364 A R f g) = (term365 A R f g).
Proof. exact (MK_COMB (@lem7201773) (@lem7201772 A R f g)). Qed.
Lemma lem7201775 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term358 A R f g s) = (term347 A R f s g).
Proof. exact (eq_refl (term358 A R f g s)). Qed.
Lemma lem7201776 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7201777 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (x : type684 A) (s : A -> Prop) : (term366 A R f g x s) = (term367 A R f g x s).
Proof. exact (MK_COMB (@lem7201775 A R f s g) (@lem7201776 A x s)). Qed.
Lemma lem7201778 {A : Type'} (x : type684 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term367 A R f g x s) = (term368 A x R f s g).
Proof. exact (eq_refl (term367 A R f g x s)). Qed.
Lemma lem7201779 {A : Type'} (x : type684 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term366 A R f g x s) = (term368 A x R f s g).
Proof. exact (TRANS (@lem7201777 A R f g x s) (@lem7201778 A x R f s g)). Qed.
Lemma lem7201780 {A : Type'} (x : type684 A) (R : type1626) (f : A -> real) (g : A -> real) : (term369 A R f g x) = (term370 A x R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7201779 A x R f s g)). Qed.
Lemma lem7201781 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7201782 {A : Type'} (x : type684 A) (R : type1626) (f : A -> real) (g : A -> real) : (term371 A R f g x) = (term372 A x R f g).
Proof. exact (MK_COMB (@lem7201781 A) (@lem7201780 A x R f g)). Qed.
Lemma lem7201783 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term373 A R f g) = (term374 A R f g).
Proof. exact (fun_ext (fun x : type684 A => @lem7201782 A x R f g)). Qed.
Lemma lem7201784 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7201785 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term356 A R f g) = (term375 A R f g).
Proof. exact (MK_COMB (@lem7201784 A) (@lem7201783 A R f g)). Qed.
Lemma lem7201786 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : ((term355 A R f g) = (term356 A R f g)) = ((term350 A R f g) = (term375 A R f g)).
Proof. exact (MK_COMB (@lem7201774 A R f g) (@lem7201785 A R f g)). Qed.
Lemma lem7201787 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term350 A R f g) = (term375 A R f g).
Proof. exact (EQ_MP (@lem7201786 A R f g) (@lem7201761 A R f g)). Qed.
Lemma lem7201788 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term306 A R f g) = (term375 A R f g).
Proof. exact (TRANS (@lem7201757 A R f g) (@lem7201787 A R f g)). Qed.
Lemma lem7201789 {A : Type'} (R : type1626) (f : A -> real) : (term307 A R f) = (term376 A R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7201788 A R f g)). Qed.
Lemma lem7201790 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7201791 {A : Type'} (R : type1626) (f : A -> real) : (term308 A R f) = (term377 A R f).
Proof. exact (MK_COMB (@lem7201790 A) (@lem7201789 A R f)). Qed.
Lemma lem7201793 {A B : Type'} (P : type1413 A B) : (term351 A B P) = (term352 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7201794 {A : Type'} (P : type707 A) : (term378 A P) = (term379 A P).
Proof. exact (@lem7201793 (A -> real) (type684 A) P). Qed.
Lemma lem7201795 {A : Type'} (R : type1626) (f : A -> real) : (term380 A R f) = (term381 A R f).
Proof. exact (@lem7201794 A (term382 A R f)). Qed.
Lemma lem7201796 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term383 A R f g) = (term374 A R f g).
Proof. exact (eq_refl (term383 A R f g)). Qed.
Lemma lem7201797 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7201798 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (x : type684 A) : (term384 A R f g x) = (term385 A R f g x).
Proof. exact (MK_COMB (@lem7201796 A R f g) (@lem7201797 A x)). Qed.
Lemma lem7201799 {A : Type'} (x : type684 A) (R : type1626) (f : A -> real) (g : A -> real) : (term385 A R f g x) = (term372 A x R f g).
Proof. exact (eq_refl (term385 A R f g x)). Qed.
Lemma lem7201800 {A : Type'} (x : type684 A) (R : type1626) (f : A -> real) (g : A -> real) : (term384 A R f g x) = (term372 A x R f g).
Proof. exact (TRANS (@lem7201798 A R f g x) (@lem7201799 A x R f g)). Qed.
Lemma lem7201801 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term386 A R f g) = (term374 A R f g).
Proof. exact (fun_ext (fun x : type684 A => @lem7201800 A x R f g)). Qed.
Lemma lem7201802 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7201803 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term387 A R f g) = (term375 A R f g).
Proof. exact (MK_COMB (@lem7201802 A) (@lem7201801 A R f g)). Qed.
Lemma lem7201804 {A : Type'} (R : type1626) (f : A -> real) : (term388 A R f) = (term376 A R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7201803 A R f g)). Qed.
Lemma lem7201805 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7201806 {A : Type'} (R : type1626) (f : A -> real) : (term380 A R f) = (term377 A R f).
Proof. exact (MK_COMB (@lem7201805 A) (@lem7201804 A R f)). Qed.
Lemma lem7201807 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7201808 {A : Type'} (R : type1626) (f : A -> real) : (term389 A R f) = (term390 A R f).
Proof. exact (MK_COMB (@lem7201807) (@lem7201806 A R f)). Qed.
Lemma lem7201809 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) : (term383 A R f g) = (term374 A R f g).
Proof. exact (eq_refl (term383 A R f g)). Qed.
Lemma lem7201810 {A : Type'} (x : type710 A) (g : A -> real) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem7201811 {A : Type'} (R : type1626) (f : A -> real) (x : type710 A) (g : A -> real) : (term391 A R f x g) = (term392 A R f x g).
Proof. exact (MK_COMB (@lem7201809 A R f g) (@lem7201810 A x g)). Qed.
Lemma lem7201812 {A : Type'} (x : type710 A) (R : type1626) (f : A -> real) (g : A -> real) : (term392 A R f x g) = (term393 A x R f g).
Proof. exact (eq_refl (term392 A R f x g)). Qed.
Lemma lem7201813 {A : Type'} (x : type710 A) (R : type1626) (f : A -> real) (g : A -> real) : (term391 A R f x g) = (term393 A x R f g).
Proof. exact (TRANS (@lem7201811 A R f x g) (@lem7201812 A x R f g)). Qed.
Lemma lem7201814 {A : Type'} (x : type710 A) (R : type1626) (f : A -> real) : (term394 A R f x) = (term395 A x R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7201813 A x R f g)). Qed.
Lemma lem7201815 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7201816 {A : Type'} (x : type710 A) (R : type1626) (f : A -> real) : (term396 A R f x) = (term397 A x R f).
Proof. exact (MK_COMB (@lem7201815 A) (@lem7201814 A x R f)). Qed.
Lemma lem7201817 {A : Type'} (R : type1626) (f : A -> real) : (term398 A R f) = (term399 A R f).
Proof. exact (fun_ext (fun x : type710 A => @lem7201816 A x R f)). Qed.
Lemma lem7201818 {A : Type'} : (@ex ((A -> real) -> (A -> Prop) -> A)) = (@ex ((A -> real) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> (A -> Prop) -> A))). Qed.
Lemma lem7201819 {A : Type'} (R : type1626) (f : A -> real) : (term381 A R f) = (term400 A R f).
Proof. exact (MK_COMB (@lem7201818 A) (@lem7201817 A R f)). Qed.
Lemma lem7201820 {A : Type'} (R : type1626) (f : A -> real) : ((term380 A R f) = (term381 A R f)) = ((term377 A R f) = (term400 A R f)).
Proof. exact (MK_COMB (@lem7201808 A R f) (@lem7201819 A R f)). Qed.
Lemma lem7201821 {A : Type'} (R : type1626) (f : A -> real) : (term377 A R f) = (term400 A R f).
Proof. exact (EQ_MP (@lem7201820 A R f) (@lem7201795 A R f)). Qed.
Lemma lem7201822 {A : Type'} (R : type1626) (f : A -> real) : (term308 A R f) = (term400 A R f).
Proof. exact (TRANS (@lem7201791 A R f) (@lem7201821 A R f)). Qed.
Lemma lem7201823 {A : Type'} (R : type1626) : (term309 A R) = (term401 A R).
Proof. exact (fun_ext (fun f : A -> real => @lem7201822 A R f)). Qed.
Lemma lem7201824 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7201825 {A : Type'} (R : type1626) : (term310 A R) = (term402 A R).
Proof. exact (MK_COMB (@lem7201824 A) (@lem7201823 A R)). Qed.
Lemma lem7201827 {A B : Type'} (P : type1413 A B) : (term351 A B P) = (term352 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7201828 {A : Type'} (P : type708 A) : (term403 A P) = (term404 A P).
Proof. exact (@lem7201827 (A -> real) (type710 A) P). Qed.
Lemma lem7201829 {A : Type'} (R : type1626) : (term405 A R) = (term406 A R).
Proof. exact (@lem7201828 A (term407 A R)). Qed.
Lemma lem7201830 {A : Type'} (R : type1626) (f : A -> real) : (term408 A R f) = (term399 A R f).
Proof. exact (eq_refl (term408 A R f)). Qed.
Lemma lem7201831 {A : Type'} (x : type710 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7201832 {A : Type'} (R : type1626) (f : A -> real) (x : type710 A) : (term409 A R f x) = (term410 A R f x).
Proof. exact (MK_COMB (@lem7201830 A R f) (@lem7201831 A x)). Qed.
Lemma lem7201833 {A : Type'} (x : type710 A) (R : type1626) (f : A -> real) : (term410 A R f x) = (term397 A x R f).
Proof. exact (eq_refl (term410 A R f x)). Qed.
Lemma lem7201834 {A : Type'} (x : type710 A) (R : type1626) (f : A -> real) : (term409 A R f x) = (term397 A x R f).
Proof. exact (TRANS (@lem7201832 A R f x) (@lem7201833 A x R f)). Qed.
Lemma lem7201835 {A : Type'} (R : type1626) (f : A -> real) : (term411 A R f) = (term399 A R f).
Proof. exact (fun_ext (fun x : type710 A => @lem7201834 A x R f)). Qed.
Lemma lem7201836 {A : Type'} : (@ex ((A -> real) -> (A -> Prop) -> A)) = (@ex ((A -> real) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> (A -> Prop) -> A))). Qed.
Lemma lem7201837 {A : Type'} (R : type1626) (f : A -> real) : (term412 A R f) = (term400 A R f).
Proof. exact (MK_COMB (@lem7201836 A) (@lem7201835 A R f)). Qed.
Lemma lem7201838 {A : Type'} (R : type1626) : (term413 A R) = (term401 A R).
Proof. exact (fun_ext (fun f : A -> real => @lem7201837 A R f)). Qed.
Lemma lem7201839 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7201840 {A : Type'} (R : type1626) : (term405 A R) = (term402 A R).
Proof. exact (MK_COMB (@lem7201839 A) (@lem7201838 A R)). Qed.
Lemma lem7201841 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7201842 {A : Type'} (R : type1626) : (term414 A R) = (term415 A R).
Proof. exact (MK_COMB (@lem7201841) (@lem7201840 A R)). Qed.
Lemma lem7201843 {A : Type'} (R : type1626) (f : A -> real) : (term408 A R f) = (term399 A R f).
Proof. exact (eq_refl (term408 A R f)). Qed.
Lemma lem7201844 {A : Type'} (x : type711 A) (f : A -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7201845 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) : (term416 A R x f) = (term417 A R x f).
Proof. exact (MK_COMB (@lem7201843 A R f) (@lem7201844 A x f)). Qed.
Lemma lem7201846 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) : (term417 A R x f) = (term418 A x R f).
Proof. exact (eq_refl (term417 A R x f)). Qed.
Lemma lem7201847 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) : (term416 A R x f) = (term418 A x R f).
Proof. exact (TRANS (@lem7201845 A R x f) (@lem7201846 A x R f)). Qed.
Lemma lem7201848 {A : Type'} (x : type711 A) (R : type1626) : (term419 A R x) = (term420 A x R).
Proof. exact (fun_ext (fun f : A -> real => @lem7201847 A x R f)). Qed.
Lemma lem7201849 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7201850 {A : Type'} (x : type711 A) (R : type1626) : (term421 A R x) = (term422 A x R).
Proof. exact (MK_COMB (@lem7201849 A) (@lem7201848 A x R)). Qed.
Lemma lem7201851 {A : Type'} (R : type1626) : (term423 A R) = (term424 A R).
Proof. exact (fun_ext (fun x : type711 A => @lem7201850 A x R)). Qed.
Lemma lem7201852 {A : Type'} : (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A)) = (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A))). Qed.
Lemma lem7201853 {A : Type'} (R : type1626) : (term406 A R) = (term425 A R).
Proof. exact (MK_COMB (@lem7201852 A) (@lem7201851 A R)). Qed.
Lemma lem7201854 {A : Type'} (R : type1626) : ((term405 A R) = (term406 A R)) = ((term402 A R) = (term425 A R)).
Proof. exact (MK_COMB (@lem7201842 A R) (@lem7201853 A R)). Qed.
Lemma lem7201855 {A : Type'} (R : type1626) : (term402 A R) = (term425 A R).
Proof. exact (EQ_MP (@lem7201854 A R) (@lem7201829 A R)). Qed.
Lemma lem7201856 {A : Type'} (R : type1626) : (term310 A R) = (term425 A R).
Proof. exact (TRANS (@lem7201825 A R) (@lem7201855 A R)). Qed.
Lemma lem7201857 (R : type1626) : (term312 R) = (term312 R).
Proof. exact (eq_refl (term312 R)). Qed.
Lemma lem7201858 {A : Type'} (R : type1626) : (term314 A R) = (term426 A R).
Proof. exact (MK_COMB (@lem7201857 R) (@lem7201856 A R)). Qed.
Lemma lem7201862 {A : Type'} (P : A -> Prop) (Q : Prop) : (term332 A P Q) = (term333 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7201863 (P : real -> Prop) (Q : Prop) : (term427 P Q) = (term428 P Q).
Proof. exact (@lem7201862 real P Q). Qed.
Lemma lem7201864 {A : Type'} (R : type1626) : (term429 A R) = (term430 A R).
Proof. exact (@lem7201863 (term283 R) (term425 A R)). Qed.
Lemma lem7201865 (R : type1626) (x1 : real) : (term431 R x1) = (term277 R x1).
Proof. exact (eq_refl (term431 R x1)). Qed.
Lemma lem7201866 (R : type1626) : (term432 R) = (term283 R).
Proof. exact (fun_ext (fun x1 : real => @lem7201865 R x1)). Qed.
Lemma lem7201867 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7201868 (R : type1626) : (term433 R) = (term284 R).
Proof. exact (MK_COMB (@lem7201867) (@lem7201866 R)). Qed.
Lemma lem7201869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7201870 (R : type1626) : (term434 R) = (term312 R).
Proof. exact (MK_COMB (@lem7201869) (@lem7201868 R)). Qed.
Lemma lem7201871 {A : Type'} (R : type1626) : (term425 A R) = (term425 A R).
Proof. exact (eq_refl (term425 A R)). Qed.
Lemma lem7201872 {A : Type'} (R : type1626) : (term429 A R) = (term426 A R).
Proof. exact (MK_COMB (@lem7201870 R) (@lem7201871 A R)). Qed.
Lemma lem7201873 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7201874 {A : Type'} (R : type1626) : (term435 A R) = (term436 A R).
Proof. exact (MK_COMB (@lem7201873) (@lem7201872 A R)). Qed.
Lemma lem7201875 (R : type1626) (x1 : real) : (term431 R x1) = (term277 R x1).
Proof. exact (eq_refl (term431 R x1)). Qed.
Lemma lem7201876 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7201877 (R : type1626) (x1 : real) : (term437 R x1) = (term438 R x1).
Proof. exact (MK_COMB (@lem7201876) (@lem7201875 R x1)). Qed.
Lemma lem7201878 {A : Type'} (R : type1626) : (term425 A R) = (term425 A R).
Proof. exact (eq_refl (term425 A R)). Qed.
Lemma lem7201879 {A : Type'} (x1 : real) (R : type1626) : (term439 A x1 R) = (term440 A x1 R).
Proof. exact (MK_COMB (@lem7201877 R x1) (@lem7201878 A R)). Qed.
Lemma lem7201880 {A : Type'} (R : type1626) : (term441 A R) = (term442 A R).
Proof. exact (fun_ext (fun x1 : real => @lem7201879 A x1 R)). Qed.
Lemma lem7201881 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7201882 {A : Type'} (R : type1626) : (term430 A R) = (term443 A R).
Proof. exact (MK_COMB (@lem7201881) (@lem7201880 A R)). Qed.
Lemma lem7201883 {A : Type'} (R : type1626) : ((term429 A R) = (term430 A R)) = ((term426 A R) = (term443 A R)).
Proof. exact (MK_COMB (@lem7201874 A R) (@lem7201882 A R)). Qed.
Lemma lem7201884 {A : Type'} (R : type1626) : (term426 A R) = (term443 A R).
Proof. exact (EQ_MP (@lem7201883 A R) (@lem7201864 A R)). Qed.
Lemma lem7201888 {A : Type'} (P : A -> Prop) (Q : Prop) : (term332 A P Q) = (term333 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7201889 (P : real -> Prop) (Q : Prop) : (term427 P Q) = (term428 P Q).
Proof. exact (@lem7201888 real P Q). Qed.
Lemma lem7201890 {A : Type'} (x1 : real) (R : type1626) : (term444 A x1 R) = (term445 A x1 R).
Proof. exact (@lem7201889 (term276 R x1) (term425 A R)). Qed.
Lemma lem7201891 (R : type1626) (x1 : real) (y1 : real) : (term446 R x1 y1) = (term270 R x1 y1).
Proof. exact (eq_refl (term446 R x1 y1)). Qed.
Lemma lem7201892 (R : type1626) (x1 : real) : (term447 R x1) = (term276 R x1).
Proof. exact (fun_ext (fun y1 : real => @lem7201891 R x1 y1)). Qed.
Lemma lem7201893 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7201894 (R : type1626) (x1 : real) : (term448 R x1) = (term277 R x1).
Proof. exact (MK_COMB (@lem7201893) (@lem7201892 R x1)). Qed.
Lemma lem7201895 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7201896 (R : type1626) (x1 : real) : (term449 R x1) = (term438 R x1).
Proof. exact (MK_COMB (@lem7201895) (@lem7201894 R x1)). Qed.
Lemma lem7201897 {A : Type'} (R : type1626) : (term425 A R) = (term425 A R).
Proof. exact (eq_refl (term425 A R)). Qed.
Lemma lem7201898 {A : Type'} (x1 : real) (R : type1626) : (term444 A x1 R) = (term440 A x1 R).
Proof. exact (MK_COMB (@lem7201896 R x1) (@lem7201897 A R)). Qed.
Lemma lem7201899 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7201900 {A : Type'} (x1 : real) (R : type1626) : (term450 A x1 R) = (term451 A x1 R).
Proof. exact (MK_COMB (@lem7201899) (@lem7201898 A x1 R)). Qed.
Lemma lem7201901 (R : type1626) (x1 : real) (y1 : real) : (term446 R x1 y1) = (term270 R x1 y1).
Proof. exact (eq_refl (term446 R x1 y1)). Qed.
Lemma lem7201902 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7201903 (R : type1626) (x1 : real) (y1 : real) : (term452 R x1 y1) = (term453 R x1 y1).
Proof. exact (MK_COMB (@lem7201902) (@lem7201901 R x1 y1)). Qed.
Lemma lem7201904 {A : Type'} (R : type1626) : (term425 A R) = (term425 A R).
Proof. exact (eq_refl (term425 A R)). Qed.
Lemma lem7201905 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : (term454 A x1 y1 R) = (term455 A x1 y1 R).
Proof. exact (MK_COMB (@lem7201903 R x1 y1) (@lem7201904 A R)). Qed.
Lemma lem7201906 {A : Type'} (x1 : real) (R : type1626) : (term456 A x1 R) = (term457 A x1 R).
Proof. exact (fun_ext (fun y1 : real => @lem7201905 A x1 y1 R)). Qed.
Lemma lem7201907 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7201908 {A : Type'} (x1 : real) (R : type1626) : (term445 A x1 R) = (term458 A x1 R).
Proof. exact (MK_COMB (@lem7201907) (@lem7201906 A x1 R)). Qed.
Lemma lem7201909 {A : Type'} (x1 : real) (R : type1626) : ((term444 A x1 R) = (term445 A x1 R)) = ((term440 A x1 R) = (term458 A x1 R)).
Proof. exact (MK_COMB (@lem7201900 A x1 R) (@lem7201908 A x1 R)). Qed.
Lemma lem7201910 {A : Type'} (x1 : real) (R : type1626) : (term440 A x1 R) = (term458 A x1 R).
Proof. exact (EQ_MP (@lem7201909 A x1 R) (@lem7201890 A x1 R)). Qed.
Lemma lem7201914 {A : Type'} (P : A -> Prop) (Q : Prop) : (term332 A P Q) = (term333 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7201915 (P : real -> Prop) (Q : Prop) : (term427 P Q) = (term428 P Q).
Proof. exact (@lem7201914 real P Q). Qed.
Lemma lem7201916 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : (term459 A x1 y1 R) = (term460 A x1 y1 R).
Proof. exact (@lem7201915 (term269 R x1 y1) (term425 A R)). Qed.
Lemma lem7201917 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term461 R x1 y1 x2) = (term263 R x1 y1 x2).
Proof. exact (eq_refl (term461 R x1 y1 x2)). Qed.
Lemma lem7201918 (R : type1626) (x1 : real) (y1 : real) : (term462 R x1 y1) = (term269 R x1 y1).
Proof. exact (fun_ext (fun x2 : real => @lem7201917 R x1 y1 x2)). Qed.
Lemma lem7201919 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7201920 (R : type1626) (x1 : real) (y1 : real) : (term463 R x1 y1) = (term270 R x1 y1).
Proof. exact (MK_COMB (@lem7201919) (@lem7201918 R x1 y1)). Qed.
Lemma lem7201921 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7201922 (R : type1626) (x1 : real) (y1 : real) : (term464 R x1 y1) = (term453 R x1 y1).
Proof. exact (MK_COMB (@lem7201921) (@lem7201920 R x1 y1)). Qed.
Lemma lem7201923 {A : Type'} (R : type1626) : (term425 A R) = (term425 A R).
Proof. exact (eq_refl (term425 A R)). Qed.
Lemma lem7201924 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : (term459 A x1 y1 R) = (term455 A x1 y1 R).
Proof. exact (MK_COMB (@lem7201922 R x1 y1) (@lem7201923 A R)). Qed.
Lemma lem7201925 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7201926 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : (term465 A x1 y1 R) = (term466 A x1 y1 R).
Proof. exact (MK_COMB (@lem7201925) (@lem7201924 A x1 y1 R)). Qed.
Lemma lem7201927 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term461 R x1 y1 x2) = (term263 R x1 y1 x2).
Proof. exact (eq_refl (term461 R x1 y1 x2)). Qed.
Lemma lem7201928 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7201929 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term467 R x1 y1 x2) = (term468 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7201928) (@lem7201927 R x1 y1 x2)). Qed.
Lemma lem7201930 {A : Type'} (R : type1626) : (term425 A R) = (term425 A R).
Proof. exact (eq_refl (term425 A R)). Qed.
Lemma lem7201931 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : (term469 A x1 y1 x2 R) = (term470 A x1 y1 x2 R).
Proof. exact (MK_COMB (@lem7201929 R x1 y1 x2) (@lem7201930 A R)). Qed.
Lemma lem7201932 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : (term471 A x1 y1 R) = (term472 A x1 y1 R).
Proof. exact (fun_ext (fun x2 : real => @lem7201931 A x1 y1 x2 R)). Qed.
Lemma lem7201933 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7201934 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : (term460 A x1 y1 R) = (term473 A x1 y1 R).
Proof. exact (MK_COMB (@lem7201933) (@lem7201932 A x1 y1 R)). Qed.
Lemma lem7201935 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : ((term459 A x1 y1 R) = (term460 A x1 y1 R)) = ((term455 A x1 y1 R) = (term473 A x1 y1 R)).
Proof. exact (MK_COMB (@lem7201926 A x1 y1 R) (@lem7201934 A x1 y1 R)). Qed.
Lemma lem7201936 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : (term455 A x1 y1 R) = (term473 A x1 y1 R).
Proof. exact (EQ_MP (@lem7201935 A x1 y1 R) (@lem7201916 A x1 y1 R)). Qed.
Lemma lem7201940 {A : Type'} (P : A -> Prop) (Q : Prop) : (term332 A P Q) = (term333 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7201941 (P : real -> Prop) (Q : Prop) : (term427 P Q) = (term428 P Q).
Proof. exact (@lem7201940 real P Q). Qed.
Lemma lem7201942 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : (term474 A x1 y1 x2 R) = (term475 A x1 y1 x2 R).
Proof. exact (@lem7201941 (term262 R x1 y1 x2) (term425 A R)). Qed.
Lemma lem7201943 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term476 R x1 y1 x2 y2) = (term253 R x1 y1 x2 y2).
Proof. exact (eq_refl (term476 R x1 y1 x2 y2)). Qed.
Lemma lem7201944 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term477 R x1 y1 x2) = (term262 R x1 y1 x2).
Proof. exact (fun_ext (fun y2 : real => @lem7201943 R x1 y1 x2 y2)). Qed.
Lemma lem7201945 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7201946 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term478 R x1 y1 x2) = (term263 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7201945) (@lem7201944 R x1 y1 x2)). Qed.
Lemma lem7201947 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7201948 (R : type1626) (x1 : real) (y1 : real) (x2 : real) : (term479 R x1 y1 x2) = (term468 R x1 y1 x2).
Proof. exact (MK_COMB (@lem7201947) (@lem7201946 R x1 y1 x2)). Qed.
Lemma lem7201949 {A : Type'} (R : type1626) : (term425 A R) = (term425 A R).
Proof. exact (eq_refl (term425 A R)). Qed.
Lemma lem7201950 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : (term474 A x1 y1 x2 R) = (term470 A x1 y1 x2 R).
Proof. exact (MK_COMB (@lem7201948 R x1 y1 x2) (@lem7201949 A R)). Qed.
Lemma lem7201951 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7201952 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : (term480 A x1 y1 x2 R) = (term481 A x1 y1 x2 R).
Proof. exact (MK_COMB (@lem7201951) (@lem7201950 A x1 y1 x2 R)). Qed.
Lemma lem7201953 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term476 R x1 y1 x2 y2) = (term253 R x1 y1 x2 y2).
Proof. exact (eq_refl (term476 R x1 y1 x2 y2)). Qed.
Lemma lem7201954 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7201955 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term482 R x1 y1 x2 y2) = (term483 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7201954) (@lem7201953 R x1 y1 x2 y2)). Qed.
Lemma lem7201956 {A : Type'} (R : type1626) : (term425 A R) = (term425 A R).
Proof. exact (eq_refl (term425 A R)). Qed.
Lemma lem7201957 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) : (term484 A x1 y1 x2 y2 R) = (term485 A x1 y1 x2 y2 R).
Proof. exact (MK_COMB (@lem7201955 R x1 y1 x2 y2) (@lem7201956 A R)). Qed.
Lemma lem7201958 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : (term486 A x1 y1 x2 R) = (term487 A x1 y1 x2 R).
Proof. exact (fun_ext (fun y2 : real => @lem7201957 A x1 y1 x2 y2 R)). Qed.
Lemma lem7201959 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7201960 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : (term475 A x1 y1 x2 R) = (term488 A x1 y1 x2 R).
Proof. exact (MK_COMB (@lem7201959) (@lem7201958 A x1 y1 x2 R)). Qed.
Lemma lem7201961 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : ((term474 A x1 y1 x2 R) = (term475 A x1 y1 x2 R)) = ((term470 A x1 y1 x2 R) = (term488 A x1 y1 x2 R)).
Proof. exact (MK_COMB (@lem7201952 A x1 y1 x2 R) (@lem7201960 A x1 y1 x2 R)). Qed.
Lemma lem7201962 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : (term470 A x1 y1 x2 R) = (term488 A x1 y1 x2 R).
Proof. exact (EQ_MP (@lem7201961 A x1 y1 x2 R) (@lem7201942 A x1 y1 x2 R)). Qed.
Lemma lem7201964 {A : Type'} (P : Prop) (Q : A -> Prop) : (term315 A P Q) = (term316 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7201965 {A : Type'} (P : Prop) (Q : type187 A) : (term489 A P Q) = (term490 A P Q).
Proof. exact (@lem7201964 (type711 A) P Q). Qed.
Lemma lem7201966 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) : (term491 A x1 y1 x2 y2 R) = (term492 A x1 y1 x2 y2 R).
Proof. exact (@lem7201965 A (term253 R x1 y1 x2 y2) (term424 A R)). Qed.
Lemma lem7201967 {A : Type'} (x : type711 A) (R : type1626) : (term493 A R x) = (term422 A x R).
Proof. exact (eq_refl (term493 A R x)). Qed.
Lemma lem7201968 {A : Type'} (R : type1626) : (term494 A R) = (term424 A R).
Proof. exact (fun_ext (fun x : type711 A => @lem7201967 A x R)). Qed.
Lemma lem7201969 {A : Type'} : (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A)) = (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A))). Qed.
Lemma lem7201970 {A : Type'} (R : type1626) : (term495 A R) = (term425 A R).
Proof. exact (MK_COMB (@lem7201969 A) (@lem7201968 A R)). Qed.
Lemma lem7201971 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term483 R x1 y1 x2 y2) = (term483 R x1 y1 x2 y2).
Proof. exact (eq_refl (term483 R x1 y1 x2 y2)). Qed.
Lemma lem7201972 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) : (term491 A x1 y1 x2 y2 R) = (term485 A x1 y1 x2 y2 R).
Proof. exact (MK_COMB (@lem7201971 R x1 y1 x2 y2) (@lem7201970 A R)). Qed.
Lemma lem7201973 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7201974 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) : (term496 A x1 y1 x2 y2 R) = (term497 A x1 y1 x2 y2 R).
Proof. exact (MK_COMB (@lem7201973) (@lem7201972 A x1 y1 x2 y2 R)). Qed.
Lemma lem7201975 {A : Type'} (x : type711 A) (R : type1626) : (term493 A R x) = (term422 A x R).
Proof. exact (eq_refl (term493 A R x)). Qed.
Lemma lem7201976 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term483 R x1 y1 x2 y2) = (term483 R x1 y1 x2 y2).
Proof. exact (eq_refl (term483 R x1 y1 x2 y2)). Qed.
Lemma lem7201977 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (x : type711 A) (R : type1626) : (term498 A x1 y1 x2 y2 R x) = (term499 A x1 y1 x2 y2 x R).
Proof. exact (MK_COMB (@lem7201976 R x1 y1 x2 y2) (@lem7201975 A x R)). Qed.
Lemma lem7201978 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) : (term500 A x1 y1 x2 y2 R) = (term501 A x1 y1 x2 y2 R).
Proof. exact (fun_ext (fun x : type711 A => @lem7201977 A x1 y1 x2 y2 x R)). Qed.
Lemma lem7201979 {A : Type'} : (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A)) = (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A))). Qed.
Lemma lem7201980 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) : (term492 A x1 y1 x2 y2 R) = (term502 A x1 y1 x2 y2 R).
Proof. exact (MK_COMB (@lem7201979 A) (@lem7201978 A x1 y1 x2 y2 R)). Qed.
Lemma lem7201981 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) : ((term491 A x1 y1 x2 y2 R) = (term492 A x1 y1 x2 y2 R)) = ((term485 A x1 y1 x2 y2 R) = (term502 A x1 y1 x2 y2 R)).
Proof. exact (MK_COMB (@lem7201974 A x1 y1 x2 y2 R) (@lem7201980 A x1 y1 x2 y2 R)). Qed.
Lemma lem7201982 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) : (term485 A x1 y1 x2 y2 R) = (term502 A x1 y1 x2 y2 R).
Proof. exact (EQ_MP (@lem7201981 A x1 y1 x2 y2 R) (@lem7201966 A x1 y1 x2 y2 R)). Qed.
Lemma lem7201983 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : (term487 A x1 y1 x2 R) = (term503 A x1 y1 x2 R).
Proof. exact (fun_ext (fun y2 : real => @lem7201982 A x1 y1 x2 y2 R)). Qed.
Lemma lem7201984 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7201985 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : (term488 A x1 y1 x2 R) = (term504 A x1 y1 x2 R).
Proof. exact (MK_COMB (@lem7201984) (@lem7201983 A x1 y1 x2 R)). Qed.
Lemma lem7201986 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) : (term470 A x1 y1 x2 R) = (term504 A x1 y1 x2 R).
Proof. exact (TRANS (@lem7201962 A x1 y1 x2 R) (@lem7201985 A x1 y1 x2 R)). Qed.
Lemma lem7201987 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : (term472 A x1 y1 R) = (term505 A x1 y1 R).
Proof. exact (fun_ext (fun x2 : real => @lem7201986 A x1 y1 x2 R)). Qed.
Lemma lem7201988 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7201989 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : (term473 A x1 y1 R) = (term506 A x1 y1 R).
Proof. exact (MK_COMB (@lem7201988) (@lem7201987 A x1 y1 R)). Qed.
Lemma lem7201990 {A : Type'} (x1 : real) (y1 : real) (R : type1626) : (term455 A x1 y1 R) = (term506 A x1 y1 R).
Proof. exact (TRANS (@lem7201936 A x1 y1 R) (@lem7201989 A x1 y1 R)). Qed.
Lemma lem7201991 {A : Type'} (x1 : real) (R : type1626) : (term457 A x1 R) = (term507 A x1 R).
Proof. exact (fun_ext (fun y1 : real => @lem7201990 A x1 y1 R)). Qed.
Lemma lem7201992 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7201993 {A : Type'} (x1 : real) (R : type1626) : (term458 A x1 R) = (term508 A x1 R).
Proof. exact (MK_COMB (@lem7201992) (@lem7201991 A x1 R)). Qed.
Lemma lem7201994 {A : Type'} (x1 : real) (R : type1626) : (term440 A x1 R) = (term508 A x1 R).
Proof. exact (TRANS (@lem7201910 A x1 R) (@lem7201993 A x1 R)). Qed.
Lemma lem7201995 {A : Type'} (R : type1626) : (term442 A R) = (term509 A R).
Proof. exact (fun_ext (fun x1 : real => @lem7201994 A x1 R)). Qed.
Lemma lem7201996 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7201997 {A : Type'} (R : type1626) : (term443 A R) = (term510 A R).
Proof. exact (MK_COMB (@lem7201996) (@lem7201995 A R)). Qed.
Lemma lem7201998 {A : Type'} (R : type1626) : (term426 A R) = (term510 A R).
Proof. exact (TRANS (@lem7201884 A R) (@lem7201997 A R)). Qed.
Lemma lem7202000 {A : Type'} (R : type1626) : (term314 A R) = (term510 A R).
Proof. exact (TRANS (@lem7201858 A R) (@lem7201998 A R)). Qed.
Lemma lem7202001 {A : Type'} (R : type1626) : (term206 A R) = (term510 A R).
Proof. exact (TRANS (@lem7201540 A R) (@lem7202000 A R)). Qed.
Lemma lem7202002 {A : Type'} (R : type1626) (h1 : term206 A R) : term510 A R.
Proof. exact (EQ_MP (@lem7202001 A R) (@lem7201299 A R h1)). Qed.
Lemma lem7202008 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7202015 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term227 A s R f g x) = (term511 A s R f g x).
Proof. exact (@lem17265 (@IN A x s) (term287 A R f g x)). Qed.
Lemma lem7202016 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term228 A s R f g) = (term512 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7202015 A s R f g x)). Qed.
Lemma lem7202017 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7202070 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term80 A s R f g) = (term513 A s R f g).
Proof. exact (MK_COMB (@lem7202017 A) (@lem7202016 A s R f g)). Qed.
Lemma lem7202071 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (h1 : term80 A s R f g) : term513 A s R f g.
Proof. exact (EQ_MP (@lem7202070 A s R f g) (@lem7201301 A s R f g h1)). Qed.
Lemma lem7202077 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term239 A R f s g) : term239 A R f s g.
Proof. exact (h1). Qed.
Lemma lem7202078 {A : Type'} (x1 : real) (R : type1626) (h1 : term508 A x1 R) : term508 A x1 R.
Proof. exact (h1). Qed.
Lemma lem7202079 {A : Type'} (x1 : real) (y1 : real) (R : type1626) (h1 : term506 A x1 y1 R) : term506 A x1 y1 R.
Proof. exact (h1). Qed.
Lemma lem7202080 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) (h1 : term504 A x1 y1 x2 R) : term504 A x1 y1 x2 R.
Proof. exact (h1). Qed.
Lemma lem7202081 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) (h1 : term502 A x1 y1 x2 y2 R) : term502 A x1 y1 x2 y2 R.
Proof. exact (h1). Qed.
Lemma lem7202082 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (x : type711 A) (R : type1626) (h1 : term499 A x1 y1 x2 y2 x R) : term499 A x1 y1 x2 y2 x R.
Proof. exact (h1). Qed.
Lemma lem7202129 (R : type1626) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7202136 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202137 (f : type1627) (x : real) : (f x) = (@I (real -> real -> real) f x).
Proof. exact (@lem7202136 real (real -> real) f x). Qed.
Lemma lem7202138 (m : real) : (real_add m) = (@I (real -> real -> real) real_add m).
Proof. exact (@lem7202137 real_add m). Qed.
Lemma lem7202139 (m' : real) : m' = m'.
Proof. exact (eq_refl m'). Qed.
Lemma lem7202140 (m : real) (m' : real) : (real_add m m') = (@I (real -> real -> real) real_add m m').
Proof. exact (MK_COMB (@lem7202138 m) (@lem7202139 m')). Qed.
Lemma lem7202142 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202143 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem7202142 real real f x). Qed.
Lemma lem7202144 (m : real) (m' : real) : (@I (real -> real -> real) real_add m m') = (term514 m m').
Proof. exact (@lem7202143 (@I (real -> real -> real) real_add m) m'). Qed.
Lemma lem7202146 (m : real) (m' : real) : (real_add m m') = (term514 m m').
Proof. exact (TRANS (@lem7202140 m m') (@lem7202144 m m')). Qed.
Lemma lem7202153 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202154 (f : type1627) (x : real) : (f x) = (@I (real -> real -> real) f x).
Proof. exact (@lem7202153 real (real -> real) f x). Qed.
Lemma lem7202155 (n : real) : (real_add n) = (@I (real -> real -> real) real_add n).
Proof. exact (@lem7202154 real_add n). Qed.
Lemma lem7202156 (n' : real) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem7202157 (n : real) (n' : real) : (real_add n n') = (@I (real -> real -> real) real_add n n').
Proof. exact (MK_COMB (@lem7202155 n) (@lem7202156 n')). Qed.
Lemma lem7202159 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202160 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem7202159 real real f x). Qed.
Lemma lem7202161 (n : real) (n' : real) : (@I (real -> real -> real) real_add n n') = (term514 n n').
Proof. exact (@lem7202160 (@I (real -> real -> real) real_add n) n'). Qed.
Lemma lem7202163 (n : real) (n' : real) : (real_add n n') = (term514 n n').
Proof. exact (TRANS (@lem7202157 n n') (@lem7202161 n n')). Qed.
Lemma lem7202164 (R : type1626) (m : real) (m' : real) : (term515 R m m') = (term516 R m m').
Proof. exact (MK_COMB (@lem7202129 R) (@lem7202146 m m')). Qed.
Lemma lem7202165 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term32 R m m' n n') = (term517 R m m' n n').
Proof. exact (MK_COMB (@lem7202164 R m m') (@lem7202163 n n')). Qed.
Lemma lem7202167 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202168 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7202167 real (real -> Prop) f x). Qed.
Lemma lem7202169 (R : type1626) (m : real) (m' : real) : (term516 R m m') = (term518 R m m').
Proof. exact (@lem7202168 R (term514 m m')). Qed.
Lemma lem7202170 (n : real) (n' : real) : (term514 n n') = (term514 n n').
Proof. exact (eq_refl (term514 n n')). Qed.
Lemma lem7202171 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term517 R m m' n n') = (term519 R m m' n n').
Proof. exact (MK_COMB (@lem7202169 R m m') (@lem7202170 n n')). Qed.
Lemma lem7202173 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202174 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7202173 real Prop f x). Qed.
Lemma lem7202175 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term519 R m m' n n') = (term520 R m m' n n').
Proof. exact (@lem7202174 (term518 R m m') (term514 n n')). Qed.
Lemma lem7202176 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term517 R m m' n n') = (term520 R m m' n n').
Proof. exact (TRANS (@lem7202171 R m m' n n') (@lem7202175 R m m' n n')). Qed.
Lemma lem7202177 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term32 R m m' n n') = (term520 R m m' n n').
Proof. exact (TRANS (@lem7202165 R m m' n n') (@lem7202176 R m m' n n')). Qed.
Lemma lem7202178 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7202185 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202186 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7202185 real (real -> Prop) f x). Qed.
Lemma lem7202187 (R : type1626) (m' : real) : (R m') = (@I (real -> real -> Prop) R m').
Proof. exact (@lem7202186 R m'). Qed.
Lemma lem7202188 (n' : real) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem7202189 (R : type1626) (m' : real) (n' : real) : (R m' n') = (@I (real -> real -> Prop) R m' n').
Proof. exact (MK_COMB (@lem7202187 R m') (@lem7202188 n')). Qed.
Lemma lem7202191 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202192 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7202191 real Prop f x). Qed.
Lemma lem7202193 (R : type1626) (m' : real) (n' : real) : (@I (real -> real -> Prop) R m' n') = (term521 R m' n').
Proof. exact (@lem7202192 (@I (real -> real -> Prop) R m') n'). Qed.
Lemma lem7202195 (R : type1626) (m' : real) (n' : real) : (R m' n') = (term521 R m' n').
Proof. exact (TRANS (@lem7202189 R m' n') (@lem7202193 R m' n')). Qed.
Lemma lem7202196 (R : type1626) (m' : real) (n' : real) : (term522 R m' n') = (term523 R m' n').
Proof. exact (MK_COMB (@lem7202178) (@lem7202195 R m' n')). Qed.
Lemma lem7202197 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7202198 (R : type1626) (m' : real) (n' : real) : (term245 R m' n') = (term524 R m' n').
Proof. exact (MK_COMB (@lem7202197) (@lem7202196 R m' n')). Qed.
Lemma lem7202199 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term240 R m m' n n') = (term525 R m m' n n').
Proof. exact (MK_COMB (@lem7202198 R m' n') (@lem7202177 R m m' n n')). Qed.
Lemma lem7202200 (R : type1626) (m : real) (m' : real) (n : real) : (term241 R m m' n) = (term526 R m m' n).
Proof. exact (fun_ext (fun n' : real => @lem7202199 R m m' n n')). Qed.
Lemma lem7202201 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7202202 (R : type1626) (m : real) (m' : real) (n : real) : (term242 R m m' n) = (term527 R m m' n).
Proof. exact (MK_COMB (@lem7202201) (@lem7202200 R m m' n)). Qed.
Lemma lem7202203 (R : type1626) (m : real) (n : real) : (term243 R m n) = (term528 R m n).
Proof. exact (fun_ext (fun m' : real => @lem7202202 R m m' n)). Qed.
Lemma lem7202204 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7202205 (R : type1626) (m : real) (n : real) : (term244 R m n) = (term529 R m n).
Proof. exact (MK_COMB (@lem7202204) (@lem7202203 R m n)). Qed.
Lemma lem7202206 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7202213 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202214 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7202213 real (real -> Prop) f x). Qed.
Lemma lem7202215 (R : type1626) (m : real) : (R m) = (@I (real -> real -> Prop) R m).
Proof. exact (@lem7202214 R m). Qed.
Lemma lem7202216 (n : real) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7202217 (R : type1626) (m : real) (n : real) : (R m n) = (@I (real -> real -> Prop) R m n).
Proof. exact (MK_COMB (@lem7202215 R m) (@lem7202216 n)). Qed.
Lemma lem7202219 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202220 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7202219 real Prop f x). Qed.
Lemma lem7202221 (R : type1626) (m : real) (n : real) : (@I (real -> real -> Prop) R m n) = (term521 R m n).
Proof. exact (@lem7202220 (@I (real -> real -> Prop) R m) n). Qed.
Lemma lem7202223 (R : type1626) (m : real) (n : real) : (R m n) = (term521 R m n).
Proof. exact (TRANS (@lem7202217 R m n) (@lem7202221 R m n)). Qed.
Lemma lem7202224 (R : type1626) (m : real) (n : real) : (term522 R m n) = (term523 R m n).
Proof. exact (MK_COMB (@lem7202206) (@lem7202223 R m n)). Qed.
Lemma lem7202225 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7202226 (R : type1626) (m : real) (n : real) : (term245 R m n) = (term524 R m n).
Proof. exact (MK_COMB (@lem7202225) (@lem7202224 R m n)). Qed.
Lemma lem7202227 (R : type1626) (m : real) (n : real) : (term247 R m n) = (term530 R m n).
Proof. exact (MK_COMB (@lem7202226 R m n) (@lem7202205 R m n)). Qed.
Lemma lem7202228 (R : type1626) (m : real) : (term248 R m) = (term531 R m).
Proof. exact (fun_ext (fun n : real => @lem7202227 R m n)). Qed.
Lemma lem7202229 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7202230 (R : type1626) (m : real) : (term249 R m) = (term532 R m).
Proof. exact (MK_COMB (@lem7202229) (@lem7202228 R m)). Qed.
Lemma lem7202231 (R : type1626) : (term250 R) = (term533 R).
Proof. exact (fun_ext (fun m : real => @lem7202230 R m)). Qed.
Lemma lem7202232 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7202233 (R : type1626) : (term251 R) = (term534 R).
Proof. exact (MK_COMB (@lem7202232) (@lem7202231 R)). Qed.
Lemma lem7202234 (R : type1626) (h1 : term75 R) : term534 R.
Proof. exact (EQ_MP (@lem7202233 R) (@lem7201446 R h1)). Qed.
Lemma lem7202239 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202240 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7202239 (A -> Prop) Prop f x). Qed.
Lemma lem7202242 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7202240 A (@FINITE A) s). Qed.
Lemma lem7202244 (R : type1626) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7202249 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202251 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7202249 A real f x). Qed.
Lemma lem7202256 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202257 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7202256 A real f x). Qed.
Lemma lem7202259 {A : Type'} (g : A -> real) (x : A) : (g x) = (@I (A -> real) g x).
Proof. exact (@lem7202257 A g x). Qed.
Lemma lem7202260 {A : Type'} (R : type1626) (f : A -> real) (x : A) : (term535 A R f x) = (term536 A R f x).
Proof. exact (MK_COMB (@lem7202244 R) (@lem7202251 A f x)). Qed.
Lemma lem7202261 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term287 A R f g x) = (term537 A R f g x).
Proof. exact (MK_COMB (@lem7202260 A R f x) (@lem7202259 A g x)). Qed.
Lemma lem7202263 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202264 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7202263 real (real -> Prop) f x). Qed.
Lemma lem7202265 {A : Type'} (R : type1626) (f : A -> real) (x : A) : (term536 A R f x) = (term538 A R f x).
Proof. exact (@lem7202264 R (@I (A -> real) f x)). Qed.
Lemma lem7202266 {A : Type'} (g : A -> real) (x : A) : (@I (A -> real) g x) = (@I (A -> real) g x).
Proof. exact (eq_refl (@I (A -> real) g x)). Qed.
Lemma lem7202267 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term537 A R f g x) = (term539 A R f g x).
Proof. exact (MK_COMB (@lem7202265 A R f x) (@lem7202266 A g x)). Qed.
Lemma lem7202269 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202270 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7202269 real Prop f x). Qed.
Lemma lem7202271 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term539 A R f g x) = (term540 A R f g x).
Proof. exact (@lem7202270 (term538 A R f x) (@I (A -> real) g x)). Qed.
Lemma lem7202272 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term537 A R f g x) = (term540 A R f g x).
Proof. exact (TRANS (@lem7202267 A R f g x) (@lem7202271 A R f g x)). Qed.
Lemma lem7202273 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term287 A R f g x) = (term540 A R f g x).
Proof. exact (TRANS (@lem7202261 A R f g x) (@lem7202272 A R f g x)). Qed.
Lemma lem7202274 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7202281 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202282 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7202281 A (type686 A) f x). Qed.
Lemma lem7202283 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem7202282 A (@IN A) x). Qed.
Lemma lem7202284 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7202285 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem7202283 A x) (@lem7202284 A s)). Qed.
Lemma lem7202287 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202288 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7202287 (A -> Prop) Prop f x). Qed.
Lemma lem7202289 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term541 A x s).
Proof. exact (@lem7202288 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem7202291 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term541 A x s).
Proof. exact (TRANS (@lem7202285 A x s) (@lem7202289 A x s)). Qed.
Lemma lem7202292 {A : Type'} (x : A) (s : A -> Prop) : (term542 A x s) = (term543 A x s).
Proof. exact (MK_COMB (@lem7202274) (@lem7202291 A x s)). Qed.
Lemma lem7202293 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7202294 {A : Type'} (x : A) (s : A -> Prop) : (term544 A x s) = (term545 A x s).
Proof. exact (MK_COMB (@lem7202293) (@lem7202292 A x s)). Qed.
Lemma lem7202295 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term511 A s R f g x) = (term546 A s R f g x).
Proof. exact (MK_COMB (@lem7202294 A x s) (@lem7202273 A R f g x)). Qed.
Lemma lem7202296 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term512 A s R f g) = (term547 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7202295 A s R f g x)). Qed.
Lemma lem7202297 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7202298 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term513 A s R f g) = (term548 A s R f g).
Proof. exact (MK_COMB (@lem7202297 A) (@lem7202296 A s R f g)). Qed.
Lemma lem7202299 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (h1 : term80 A s R f g) : term548 A s R f g.
Proof. exact (EQ_MP (@lem7202298 A s R f g) (@lem7202071 A s R f g h1)). Qed.
Lemma lem7202300 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7202301 (R : type1626) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7202308 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202309 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7202308 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7202310 {A : Type'} (s : A -> Prop) : (@sum A s) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s).
Proof. exact (@lem7202309 A (@sum A) s). Qed.
Lemma lem7202311 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7202312 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f).
Proof. exact (MK_COMB (@lem7202310 A s) (@lem7202311 A f)). Qed.
Lemma lem7202314 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202315 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7202314 (A -> real) real f x). Qed.
Lemma lem7202316 {A : Type'} (s : A -> Prop) (f : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f) = (term549 A s f).
Proof. exact (@lem7202315 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s) f). Qed.
Lemma lem7202318 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (term549 A s f).
Proof. exact (TRANS (@lem7202312 A s f) (@lem7202316 A s f)). Qed.
Lemma lem7202325 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202326 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7202325 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7202327 {A : Type'} (s : A -> Prop) : (@sum A s) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s).
Proof. exact (@lem7202326 A (@sum A) s). Qed.
Lemma lem7202328 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7202329 {A : Type'} (s : A -> Prop) (g : A -> real) : (@sum A s g) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s g).
Proof. exact (MK_COMB (@lem7202327 A s) (@lem7202328 A g)). Qed.
Lemma lem7202331 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202332 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7202331 (A -> real) real f x). Qed.
Lemma lem7202333 {A : Type'} (s : A -> Prop) (g : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s g) = (term549 A s g).
Proof. exact (@lem7202332 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s) g). Qed.
Lemma lem7202335 {A : Type'} (s : A -> Prop) (g : A -> real) : (@sum A s g) = (term549 A s g).
Proof. exact (TRANS (@lem7202329 A s g) (@lem7202333 A s g)). Qed.
Lemma lem7202336 {A : Type'} (R : type1626) (s : A -> Prop) (f : A -> real) : (term190 A R s f) = (term550 A R s f).
Proof. exact (MK_COMB (@lem7202301 R) (@lem7202318 A s f)). Qed.
Lemma lem7202337 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term551 A R f s g).
Proof. exact (MK_COMB (@lem7202336 A R s f) (@lem7202335 A s g)). Qed.
Lemma lem7202339 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202340 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7202339 real (real -> Prop) f x). Qed.
Lemma lem7202341 {A : Type'} (R : type1626) (s : A -> Prop) (f : A -> real) : (term550 A R s f) = (term552 A R s f).
Proof. exact (@lem7202340 R (term549 A s f)). Qed.
Lemma lem7202342 {A : Type'} (s : A -> Prop) (g : A -> real) : (term549 A s g) = (term549 A s g).
Proof. exact (eq_refl (term549 A s g)). Qed.
Lemma lem7202343 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term551 A R f s g) = (term553 A R f s g).
Proof. exact (MK_COMB (@lem7202341 A R s f) (@lem7202342 A s g)). Qed.
Lemma lem7202345 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202346 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7202345 real Prop f x). Qed.
Lemma lem7202347 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term553 A R f s g) = (term554 A R f s g).
Proof. exact (@lem7202346 (term552 A R s f) (term549 A s g)). Qed.
Lemma lem7202348 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term551 A R f s g) = (term554 A R f s g).
Proof. exact (TRANS (@lem7202343 A R f s g) (@lem7202347 A R f s g)). Qed.
Lemma lem7202349 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term554 A R f s g).
Proof. exact (TRANS (@lem7202337 A R f s g) (@lem7202348 A R f s g)). Qed.
Lemma lem7202350 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term239 A R f s g) = (term555 A R f s g).
Proof. exact (MK_COMB (@lem7202300) (@lem7202349 A R f s g)). Qed.
Lemma lem7202352 (R : type1626) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7202359 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202360 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7202359 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7202361 {A : Type'} (s : A -> Prop) : (@sum A s) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s).
Proof. exact (@lem7202360 A (@sum A) s). Qed.
Lemma lem7202362 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7202363 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f).
Proof. exact (MK_COMB (@lem7202361 A s) (@lem7202362 A f)). Qed.
Lemma lem7202365 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202366 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7202365 (A -> real) real f x). Qed.
Lemma lem7202367 {A : Type'} (s : A -> Prop) (f : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f) = (term549 A s f).
Proof. exact (@lem7202366 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s) f). Qed.
Lemma lem7202369 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (term549 A s f).
Proof. exact (TRANS (@lem7202363 A s f) (@lem7202367 A s f)). Qed.
Lemma lem7202376 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202377 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7202376 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7202378 {A : Type'} (s : A -> Prop) : (@sum A s) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s).
Proof. exact (@lem7202377 A (@sum A) s). Qed.
Lemma lem7202379 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7202380 {A : Type'} (s : A -> Prop) (g : A -> real) : (@sum A s g) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s g).
Proof. exact (MK_COMB (@lem7202378 A s) (@lem7202379 A g)). Qed.
Lemma lem7202382 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202383 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7202382 (A -> real) real f x). Qed.
Lemma lem7202384 {A : Type'} (s : A -> Prop) (g : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s g) = (term549 A s g).
Proof. exact (@lem7202383 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s) g). Qed.
Lemma lem7202386 {A : Type'} (s : A -> Prop) (g : A -> real) : (@sum A s g) = (term549 A s g).
Proof. exact (TRANS (@lem7202380 A s g) (@lem7202384 A s g)). Qed.
Lemma lem7202387 {A : Type'} (R : type1626) (s : A -> Prop) (f : A -> real) : (term190 A R s f) = (term550 A R s f).
Proof. exact (MK_COMB (@lem7202352 R) (@lem7202369 A s f)). Qed.
Lemma lem7202388 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term551 A R f s g).
Proof. exact (MK_COMB (@lem7202387 A R s f) (@lem7202386 A s g)). Qed.
Lemma lem7202390 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202391 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7202390 real (real -> Prop) f x). Qed.
Lemma lem7202392 {A : Type'} (R : type1626) (s : A -> Prop) (f : A -> real) : (term550 A R s f) = (term552 A R s f).
Proof. exact (@lem7202391 R (term549 A s f)). Qed.
Lemma lem7202393 {A : Type'} (s : A -> Prop) (g : A -> real) : (term549 A s g) = (term549 A s g).
Proof. exact (eq_refl (term549 A s g)). Qed.
Lemma lem7202394 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term551 A R f s g) = (term553 A R f s g).
Proof. exact (MK_COMB (@lem7202392 A R s f) (@lem7202393 A s g)). Qed.
Lemma lem7202396 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202397 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7202396 real Prop f x). Qed.
Lemma lem7202398 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term553 A R f s g) = (term554 A R f s g).
Proof. exact (@lem7202397 (term552 A R s f) (term549 A s g)). Qed.
Lemma lem7202399 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term551 A R f s g) = (term554 A R f s g).
Proof. exact (TRANS (@lem7202394 A R f s g) (@lem7202398 A R f s g)). Qed.
Lemma lem7202400 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term25 A R f s g) = (term554 A R f s g).
Proof. exact (TRANS (@lem7202388 A R f s g) (@lem7202399 A R f s g)). Qed.
Lemma lem7202401 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7202402 (R : type1626) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7202403 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7202412 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202413 {A : Type'} (f : type711 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7202412 (A -> real) (type710 A) f x). Qed.
Lemma lem7202414 {A : Type'} (x : type711 A) (f : A -> real) : (x f) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f).
Proof. exact (@lem7202413 A x f). Qed.
Lemma lem7202415 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7202416 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) : (x f g) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f g).
Proof. exact (MK_COMB (@lem7202414 A x f) (@lem7202415 A g)). Qed.
Lemma lem7202418 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202419 {A : Type'} (f : type710 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7202418 (A -> real) (type684 A) f x). Qed.
Lemma lem7202420 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) : (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f g) = (term556 A x f g).
Proof. exact (@lem7202419 A (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f) g). Qed.
Lemma lem7202421 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) : (x f g) = (term556 A x f g).
Proof. exact (TRANS (@lem7202416 A x f g) (@lem7202420 A x f g)). Qed.
Lemma lem7202422 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7202423 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (x f g s) = (term557 A x f g s).
Proof. exact (MK_COMB (@lem7202421 A x f g) (@lem7202422 A s)). Qed.
Lemma lem7202425 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202426 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7202425 (A -> Prop) A f x). Qed.
Lemma lem7202427 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term557 A x f g s) = (term558 A x f g s).
Proof. exact (@lem7202426 A (term556 A x f g) s). Qed.
Lemma lem7202429 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (x f g s) = (term558 A x f g s).
Proof. exact (TRANS (@lem7202423 A x f g s) (@lem7202427 A x f g s)). Qed.
Lemma lem7202430 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term559 A x f g s) = (term560 A x f g s).
Proof. exact (MK_COMB (@lem7202403 A f) (@lem7202429 A x f g s)). Qed.
Lemma lem7202432 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202433 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7202432 A real f x). Qed.
Lemma lem7202434 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term560 A x f g s) = (term561 A x f g s).
Proof. exact (@lem7202433 A f (term558 A x f g s)). Qed.
Lemma lem7202435 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term559 A x f g s) = (term561 A x f g s).
Proof. exact (TRANS (@lem7202430 A x f g s) (@lem7202434 A x f g s)). Qed.
Lemma lem7202436 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7202445 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202446 {A : Type'} (f : type711 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7202445 (A -> real) (type710 A) f x). Qed.
Lemma lem7202447 {A : Type'} (x : type711 A) (f : A -> real) : (x f) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f).
Proof. exact (@lem7202446 A x f). Qed.
Lemma lem7202448 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7202449 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) : (x f g) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f g).
Proof. exact (MK_COMB (@lem7202447 A x f) (@lem7202448 A g)). Qed.
Lemma lem7202451 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202452 {A : Type'} (f : type710 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7202451 (A -> real) (type684 A) f x). Qed.
Lemma lem7202453 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) : (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f g) = (term556 A x f g).
Proof. exact (@lem7202452 A (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f) g). Qed.
Lemma lem7202454 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) : (x f g) = (term556 A x f g).
Proof. exact (TRANS (@lem7202449 A x f g) (@lem7202453 A x f g)). Qed.
Lemma lem7202455 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7202456 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (x f g s) = (term557 A x f g s).
Proof. exact (MK_COMB (@lem7202454 A x f g) (@lem7202455 A s)). Qed.
Lemma lem7202458 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202459 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7202458 (A -> Prop) A f x). Qed.
Lemma lem7202460 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term557 A x f g s) = (term558 A x f g s).
Proof. exact (@lem7202459 A (term556 A x f g) s). Qed.
Lemma lem7202462 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (x f g s) = (term558 A x f g s).
Proof. exact (TRANS (@lem7202456 A x f g s) (@lem7202460 A x f g s)). Qed.
Lemma lem7202463 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term562 A x f g s) = (term563 A x f g s).
Proof. exact (MK_COMB (@lem7202436 A g) (@lem7202462 A x f g s)). Qed.
Lemma lem7202465 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202466 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7202465 A real f x). Qed.
Lemma lem7202467 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term563 A x f g s) = (term564 A x f g s).
Proof. exact (@lem7202466 A g (term558 A x f g s)). Qed.
Lemma lem7202468 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term562 A x f g s) = (term564 A x f g s).
Proof. exact (TRANS (@lem7202463 A x f g s) (@lem7202467 A x f g s)). Qed.
Lemma lem7202469 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term565 A R x f g s) = (term566 A R x f g s).
Proof. exact (MK_COMB (@lem7202402 R) (@lem7202435 A x f g s)). Qed.
Lemma lem7202470 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term567 A R x f g s) = (term568 A R x f g s).
Proof. exact (MK_COMB (@lem7202469 A R x f g s) (@lem7202468 A x f g s)). Qed.
Lemma lem7202472 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202473 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7202472 real (real -> Prop) f x). Qed.
Lemma lem7202474 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term566 A R x f g s) = (term569 A R x f g s).
Proof. exact (@lem7202473 R (term561 A x f g s)). Qed.
Lemma lem7202475 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term564 A x f g s) = (term564 A x f g s).
Proof. exact (eq_refl (term564 A x f g s)). Qed.
Lemma lem7202476 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term568 A R x f g s) = (term570 A R x f g s).
Proof. exact (MK_COMB (@lem7202474 A R x f g s) (@lem7202475 A x f g s)). Qed.
Lemma lem7202478 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202479 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7202478 real Prop f x). Qed.
Lemma lem7202480 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term570 A R x f g s) = (term571 A R x f g s).
Proof. exact (@lem7202479 (term569 A R x f g s) (term564 A x f g s)). Qed.
Lemma lem7202481 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term568 A R x f g s) = (term571 A R x f g s).
Proof. exact (TRANS (@lem7202476 A R x f g s) (@lem7202480 A R x f g s)). Qed.
Lemma lem7202482 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term567 A R x f g s) = (term571 A R x f g s).
Proof. exact (TRANS (@lem7202470 A R x f g s) (@lem7202481 A R x f g s)). Qed.
Lemma lem7202483 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term572 A R x f g s) = (term573 A R x f g s).
Proof. exact (MK_COMB (@lem7202401) (@lem7202482 A R x f g s)). Qed.
Lemma lem7202484 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem7202493 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202494 {A : Type'} (f : type711 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7202493 (A -> real) (type710 A) f x). Qed.
Lemma lem7202495 {A : Type'} (x : type711 A) (f : A -> real) : (x f) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f).
Proof. exact (@lem7202494 A x f). Qed.
Lemma lem7202496 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7202497 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) : (x f g) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f g).
Proof. exact (MK_COMB (@lem7202495 A x f) (@lem7202496 A g)). Qed.
Lemma lem7202499 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202500 {A : Type'} (f : type710 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7202499 (A -> real) (type684 A) f x). Qed.
Lemma lem7202501 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) : (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f g) = (term556 A x f g).
Proof. exact (@lem7202500 A (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x f) g). Qed.
Lemma lem7202502 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) : (x f g) = (term556 A x f g).
Proof. exact (TRANS (@lem7202497 A x f g) (@lem7202501 A x f g)). Qed.
Lemma lem7202503 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7202504 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (x f g s) = (term557 A x f g s).
Proof. exact (MK_COMB (@lem7202502 A x f g) (@lem7202503 A s)). Qed.
Lemma lem7202506 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202507 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7202506 (A -> Prop) A f x). Qed.
Lemma lem7202508 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term557 A x f g s) = (term558 A x f g s).
Proof. exact (@lem7202507 A (term556 A x f g) s). Qed.
Lemma lem7202510 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (x f g s) = (term558 A x f g s).
Proof. exact (TRANS (@lem7202504 A x f g s) (@lem7202508 A x f g s)). Qed.
Lemma lem7202511 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7202512 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term574 A x f g s) = (term575 A x f g s).
Proof. exact (MK_COMB (@lem7202484 A) (@lem7202510 A x f g s)). Qed.
Lemma lem7202513 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term576 A x f g s) = (term577 A x f g s).
Proof. exact (MK_COMB (@lem7202512 A x f g s) (@lem7202511 A s)). Qed.
Lemma lem7202515 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202516 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7202515 A (type686 A) f x). Qed.
Lemma lem7202517 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term575 A x f g s) = (term578 A x f g s).
Proof. exact (@lem7202516 A (@IN A) (term558 A x f g s)). Qed.
Lemma lem7202518 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7202519 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term577 A x f g s) = (term579 A x f g s).
Proof. exact (MK_COMB (@lem7202517 A x f g s) (@lem7202518 A s)). Qed.
Lemma lem7202521 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202522 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7202521 (A -> Prop) Prop f x). Qed.
Lemma lem7202523 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term579 A x f g s) = (term580 A x f g s).
Proof. exact (@lem7202522 A (term578 A x f g s) s). Qed.
Lemma lem7202524 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term577 A x f g s) = (term580 A x f g s).
Proof. exact (TRANS (@lem7202519 A x f g s) (@lem7202523 A x f g s)). Qed.
Lemma lem7202525 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term576 A x f g s) = (term580 A x f g s).
Proof. exact (TRANS (@lem7202513 A x f g s) (@lem7202524 A x f g s)). Qed.
Lemma lem7202526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7202527 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term581 A x f g s) = (term582 A x f g s).
Proof. exact (MK_COMB (@lem7202526) (@lem7202525 A x f g s)). Qed.
Lemma lem7202528 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term583 A R x f g s) = (term584 A R x f g s).
Proof. exact (MK_COMB (@lem7202527 A x f g s) (@lem7202483 A R x f g s)). Qed.
Lemma lem7202529 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7202534 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202535 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7202534 (A -> Prop) Prop f x). Qed.
Lemma lem7202537 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7202535 A (@FINITE A) s). Qed.
Lemma lem7202538 {A : Type'} (s : A -> Prop) : (term319 A s) = (term585 A s).
Proof. exact (MK_COMB (@lem7202529) (@lem7202537 A s)). Qed.
Lemma lem7202539 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7202540 {A : Type'} (s : A -> Prop) : (term297 A s) = (term586 A s).
Proof. exact (MK_COMB (@lem7202539) (@lem7202538 A s)). Qed.
Lemma lem7202541 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term587 A R x f g s) = (term588 A R x f g s).
Proof. exact (MK_COMB (@lem7202540 A s) (@lem7202528 A R x f g s)). Qed.
Lemma lem7202542 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7202543 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term589 A R x f g s) = (term590 A R x f g s).
Proof. exact (MK_COMB (@lem7202542) (@lem7202541 A R x f g s)). Qed.
Lemma lem7202544 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term591 A x R f s g) = (term592 A x R f s g).
Proof. exact (MK_COMB (@lem7202543 A R x f g s) (@lem7202400 A R f s g)). Qed.
Lemma lem7202545 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (g : A -> real) : (term593 A x R f g) = (term594 A x R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7202544 A x R f s g)). Qed.
Lemma lem7202546 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7202547 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (g : A -> real) : (term595 A x R f g) = (term596 A x R f g).
Proof. exact (MK_COMB (@lem7202546 A) (@lem7202545 A x R f g)). Qed.
Lemma lem7202548 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) : (term597 A x R f) = (term598 A x R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7202547 A x R f g)). Qed.
Lemma lem7202549 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7202550 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) : (term418 A x R f) = (term599 A x R f).
Proof. exact (MK_COMB (@lem7202549 A) (@lem7202548 A x R f)). Qed.
Lemma lem7202551 {A : Type'} (x : type711 A) (R : type1626) : (term420 A x R) = (term600 A x R).
Proof. exact (fun_ext (fun f : A -> real => @lem7202550 A x R f)). Qed.
Lemma lem7202552 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7202553 {A : Type'} (x : type711 A) (R : type1626) : (term422 A x R) = (term601 A x R).
Proof. exact (MK_COMB (@lem7202552 A) (@lem7202551 A x R)). Qed.
Lemma lem7202554 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7202555 (R : type1626) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem7202562 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202563 (f : type1627) (x : real) : (f x) = (@I (real -> real -> real) f x).
Proof. exact (@lem7202562 real (real -> real) f x). Qed.
Lemma lem7202564 (x1 : real) : (real_add x1) = (@I (real -> real -> real) real_add x1).
Proof. exact (@lem7202563 real_add x1). Qed.
Lemma lem7202565 (y1 : real) : y1 = y1.
Proof. exact (eq_refl y1). Qed.
Lemma lem7202566 (x1 : real) (y1 : real) : (real_add x1 y1) = (@I (real -> real -> real) real_add x1 y1).
Proof. exact (MK_COMB (@lem7202564 x1) (@lem7202565 y1)). Qed.
Lemma lem7202568 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202569 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem7202568 real real f x). Qed.
Lemma lem7202570 (x1 : real) (y1 : real) : (@I (real -> real -> real) real_add x1 y1) = (term514 x1 y1).
Proof. exact (@lem7202569 (@I (real -> real -> real) real_add x1) y1). Qed.
Lemma lem7202572 (x1 : real) (y1 : real) : (real_add x1 y1) = (term514 x1 y1).
Proof. exact (TRANS (@lem7202566 x1 y1) (@lem7202570 x1 y1)). Qed.
Lemma lem7202579 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202580 (f : type1627) (x : real) : (f x) = (@I (real -> real -> real) f x).
Proof. exact (@lem7202579 real (real -> real) f x). Qed.
Lemma lem7202581 (x2 : real) : (real_add x2) = (@I (real -> real -> real) real_add x2).
Proof. exact (@lem7202580 real_add x2). Qed.
Lemma lem7202582 (y2 : real) : y2 = y2.
Proof. exact (eq_refl y2). Qed.
Lemma lem7202583 (x2 : real) (y2 : real) : (real_add x2 y2) = (@I (real -> real -> real) real_add x2 y2).
Proof. exact (MK_COMB (@lem7202581 x2) (@lem7202582 y2)). Qed.
Lemma lem7202585 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202586 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem7202585 real real f x). Qed.
Lemma lem7202587 (x2 : real) (y2 : real) : (@I (real -> real -> real) real_add x2 y2) = (term514 x2 y2).
Proof. exact (@lem7202586 (@I (real -> real -> real) real_add x2) y2). Qed.
Lemma lem7202589 (x2 : real) (y2 : real) : (real_add x2 y2) = (term514 x2 y2).
Proof. exact (TRANS (@lem7202583 x2 y2) (@lem7202587 x2 y2)). Qed.
Lemma lem7202590 (R : type1626) (x1 : real) (y1 : real) : (term515 R x1 y1) = (term516 R x1 y1).
Proof. exact (MK_COMB (@lem7202555 R) (@lem7202572 x1 y1)). Qed.
Lemma lem7202591 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term32 R x1 y1 x2 y2) = (term517 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7202590 R x1 y1) (@lem7202589 x2 y2)). Qed.
Lemma lem7202593 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202594 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7202593 real (real -> Prop) f x). Qed.
Lemma lem7202595 (R : type1626) (x1 : real) (y1 : real) : (term516 R x1 y1) = (term518 R x1 y1).
Proof. exact (@lem7202594 R (term514 x1 y1)). Qed.
Lemma lem7202596 (x2 : real) (y2 : real) : (term514 x2 y2) = (term514 x2 y2).
Proof. exact (eq_refl (term514 x2 y2)). Qed.
Lemma lem7202597 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term517 R x1 y1 x2 y2) = (term519 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7202595 R x1 y1) (@lem7202596 x2 y2)). Qed.
Lemma lem7202599 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202600 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7202599 real Prop f x). Qed.
Lemma lem7202601 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term519 R x1 y1 x2 y2) = (term520 R x1 y1 x2 y2).
Proof. exact (@lem7202600 (term518 R x1 y1) (term514 x2 y2)). Qed.
Lemma lem7202602 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term517 R x1 y1 x2 y2) = (term520 R x1 y1 x2 y2).
Proof. exact (TRANS (@lem7202597 R x1 y1 x2 y2) (@lem7202601 R x1 y1 x2 y2)). Qed.
Lemma lem7202603 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term32 R x1 y1 x2 y2) = (term520 R x1 y1 x2 y2).
Proof. exact (TRANS (@lem7202591 R x1 y1 x2 y2) (@lem7202602 R x1 y1 x2 y2)). Qed.
Lemma lem7202604 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term602 R x1 y1 x2 y2) = (term603 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7202554) (@lem7202603 R x1 y1 x2 y2)). Qed.
Lemma lem7202611 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202612 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7202611 real (real -> Prop) f x). Qed.
Lemma lem7202613 (R : type1626) (y1 : real) : (R y1) = (@I (real -> real -> Prop) R y1).
Proof. exact (@lem7202612 R y1). Qed.
Lemma lem7202614 (y2 : real) : y2 = y2.
Proof. exact (eq_refl y2). Qed.
Lemma lem7202615 (R : type1626) (y1 : real) (y2 : real) : (R y1 y2) = (@I (real -> real -> Prop) R y1 y2).
Proof. exact (MK_COMB (@lem7202613 R y1) (@lem7202614 y2)). Qed.
Lemma lem7202617 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202618 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7202617 real Prop f x). Qed.
Lemma lem7202619 (R : type1626) (y1 : real) (y2 : real) : (@I (real -> real -> Prop) R y1 y2) = (term521 R y1 y2).
Proof. exact (@lem7202618 (@I (real -> real -> Prop) R y1) y2). Qed.
Lemma lem7202621 (R : type1626) (y1 : real) (y2 : real) : (R y1 y2) = (term521 R y1 y2).
Proof. exact (TRANS (@lem7202615 R y1 y2) (@lem7202619 R y1 y2)). Qed.
Lemma lem7202628 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202629 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7202628 real (real -> Prop) f x). Qed.
Lemma lem7202630 (R : type1626) (x1 : real) : (R x1) = (@I (real -> real -> Prop) R x1).
Proof. exact (@lem7202629 R x1). Qed.
Lemma lem7202631 (x2 : real) : x2 = x2.
Proof. exact (eq_refl x2). Qed.
Lemma lem7202632 (R : type1626) (x1 : real) (x2 : real) : (R x1 x2) = (@I (real -> real -> Prop) R x1 x2).
Proof. exact (MK_COMB (@lem7202630 R x1) (@lem7202631 x2)). Qed.
Lemma lem7202634 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7202635 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7202634 real Prop f x). Qed.
Lemma lem7202636 (R : type1626) (x1 : real) (x2 : real) : (@I (real -> real -> Prop) R x1 x2) = (term521 R x1 x2).
Proof. exact (@lem7202635 (@I (real -> real -> Prop) R x1) x2). Qed.
Lemma lem7202638 (R : type1626) (x1 : real) (x2 : real) : (R x1 x2) = (term521 R x1 x2).
Proof. exact (TRANS (@lem7202632 R x1 x2) (@lem7202636 R x1 x2)). Qed.
Lemma lem7202639 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7202640 (R : type1626) (x1 : real) (x2 : real) : (term604 R x1 x2) = (term605 R x1 x2).
Proof. exact (MK_COMB (@lem7202639) (@lem7202638 R x1 x2)). Qed.
Lemma lem7202641 (x1 : real) (x2 : real) (R : type1626) (y1 : real) (y2 : real) : (term254 x1 x2 R y1 y2) = (term606 x1 x2 R y1 y2).
Proof. exact (MK_COMB (@lem7202640 R x1 x2) (@lem7202621 R y1 y2)). Qed.
Lemma lem7202642 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7202643 (x1 : real) (x2 : real) (R : type1626) (y1 : real) (y2 : real) : (term607 x1 x2 R y1 y2) = (term608 x1 x2 R y1 y2).
Proof. exact (MK_COMB (@lem7202642) (@lem7202641 x1 x2 R y1 y2)). Qed.
Lemma lem7202644 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term253 R x1 y1 x2 y2) = (term609 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7202643 x1 x2 R y1 y2) (@lem7202604 R x1 y1 x2 y2)). Qed.
Lemma lem7202645 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7202646 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term483 R x1 y1 x2 y2) = (term610 R x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem7202645) (@lem7202644 R x1 y1 x2 y2)). Qed.
Lemma lem7202647 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (x : type711 A) (R : type1626) : (term499 A x1 y1 x2 y2 x R) = (term611 A x1 y1 x2 y2 x R).
Proof. exact (MK_COMB (@lem7202646 R x1 y1 x2 y2) (@lem7202553 A x R)). Qed.
Lemma lem7202648 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (x : type711 A) (R : type1626) (h1 : term499 A x1 y1 x2 y2 x R) : term611 A x1 y1 x2 y2 x R.
Proof. exact (EQ_MP (@lem7202647 A x1 y1 x2 y2 x R) (@lem7202082 A x1 y1 x2 y2 x R h1)). Qed.
Lemma lem7202649 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term609 R x1 y1 x2 y2) : term609 R x1 y1 x2 y2.
Proof. exact (h1). Qed.
Lemma lem7202650 {A : Type'} (x : type711 A) (R : type1626) (h1 : term601 A x R) : term601 A x R.
Proof. exact (h1). Qed.
Lemma lem7202652 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term609 R x1 y1 x2 y2) : term606 x1 x2 R y1 y2.
Proof. exact (proj1 (@lem7202649 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7202660 {A : Type'} (P : Prop) (Q : A -> Prop) : (term612 A P Q) = (term613 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7202661 (P : Prop) (Q : real -> Prop) : (term614 P Q) = (term615 P Q).
Proof. exact (@lem7202660 real P Q). Qed.
Lemma lem7202662 (R : type1626) (m : real) (n : real) : (term616 R m n) = (term617 R m n).
Proof. exact (@lem7202661 (term523 R m n) (term528 R m n)). Qed.
Lemma lem7202663 (R : type1626) (m : real) (m' : real) (n : real) : (term618 R m n m') = (term527 R m m' n).
Proof. exact (eq_refl (term618 R m n m')). Qed.
Lemma lem7202664 (R : type1626) (m : real) (n : real) : (term619 R m n) = (term528 R m n).
Proof. exact (fun_ext (fun m' : real => @lem7202663 R m m' n)). Qed.
Lemma lem7202665 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7202666 (R : type1626) (m : real) (n : real) : (term620 R m n) = (term529 R m n).
Proof. exact (MK_COMB (@lem7202665) (@lem7202664 R m n)). Qed.
Lemma lem7202667 (R : type1626) (m : real) (n : real) : (term524 R m n) = (term524 R m n).
Proof. exact (eq_refl (term524 R m n)). Qed.
Lemma lem7202668 (R : type1626) (m : real) (n : real) : (term616 R m n) = (term530 R m n).
Proof. exact (MK_COMB (@lem7202667 R m n) (@lem7202666 R m n)). Qed.
Lemma lem7202669 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7202670 (R : type1626) (m : real) (n : real) : (term621 R m n) = (term622 R m n).
Proof. exact (MK_COMB (@lem7202669) (@lem7202668 R m n)). Qed.
Lemma lem7202671 (R : type1626) (m : real) (m' : real) (n : real) : (term618 R m n m') = (term527 R m m' n).
Proof. exact (eq_refl (term618 R m n m')). Qed.
Lemma lem7202672 (R : type1626) (m : real) (n : real) : (term524 R m n) = (term524 R m n).
Proof. exact (eq_refl (term524 R m n)). Qed.
Lemma lem7202673 (R : type1626) (m : real) (m' : real) (n : real) : (term623 R m n m') = (term624 R m m' n).
Proof. exact (MK_COMB (@lem7202672 R m n) (@lem7202671 R m m' n)). Qed.
Lemma lem7202674 (R : type1626) (m : real) (n : real) : (term625 R m n) = (term626 R m n).
Proof. exact (fun_ext (fun m' : real => @lem7202673 R m m' n)). Qed.
Lemma lem7202675 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7202676 (R : type1626) (m : real) (n : real) : (term617 R m n) = (term627 R m n).
Proof. exact (MK_COMB (@lem7202675) (@lem7202674 R m n)). Qed.
Lemma lem7202677 (R : type1626) (m : real) (n : real) : ((term616 R m n) = (term617 R m n)) = ((term530 R m n) = (term627 R m n)).
Proof. exact (MK_COMB (@lem7202670 R m n) (@lem7202676 R m n)). Qed.
Lemma lem7202678 (R : type1626) (m : real) (n : real) : (term530 R m n) = (term627 R m n).
Proof. exact (EQ_MP (@lem7202677 R m n) (@lem7202662 R m n)). Qed.
Lemma lem7202680 {A : Type'} (P : Prop) (Q : A -> Prop) : (term612 A P Q) = (term613 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7202681 (P : Prop) (Q : real -> Prop) : (term614 P Q) = (term615 P Q).
Proof. exact (@lem7202680 real P Q). Qed.
Lemma lem7202682 (R : type1626) (m : real) (m' : real) (n : real) : (term628 R m m' n) = (term629 R m m' n).
Proof. exact (@lem7202681 (term523 R m n) (term526 R m m' n)). Qed.
Lemma lem7202683 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term630 R m m' n n') = (term525 R m m' n n').
Proof. exact (eq_refl (term630 R m m' n n')). Qed.
Lemma lem7202684 (R : type1626) (m : real) (m' : real) (n : real) : (term631 R m m' n) = (term526 R m m' n).
Proof. exact (fun_ext (fun n' : real => @lem7202683 R m m' n n')). Qed.
Lemma lem7202685 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7202686 (R : type1626) (m : real) (m' : real) (n : real) : (term632 R m m' n) = (term527 R m m' n).
Proof. exact (MK_COMB (@lem7202685) (@lem7202684 R m m' n)). Qed.
Lemma lem7202687 (R : type1626) (m : real) (n : real) : (term524 R m n) = (term524 R m n).
Proof. exact (eq_refl (term524 R m n)). Qed.
Lemma lem7202688 (R : type1626) (m : real) (m' : real) (n : real) : (term628 R m m' n) = (term624 R m m' n).
Proof. exact (MK_COMB (@lem7202687 R m n) (@lem7202686 R m m' n)). Qed.
Lemma lem7202689 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7202690 (R : type1626) (m : real) (m' : real) (n : real) : (term633 R m m' n) = (term634 R m m' n).
Proof. exact (MK_COMB (@lem7202689) (@lem7202688 R m m' n)). Qed.
Lemma lem7202691 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term630 R m m' n n') = (term525 R m m' n n').
Proof. exact (eq_refl (term630 R m m' n n')). Qed.
Lemma lem7202692 (R : type1626) (m : real) (n : real) : (term524 R m n) = (term524 R m n).
Proof. exact (eq_refl (term524 R m n)). Qed.
Lemma lem7202693 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term635 R m m' n n') = (term636 R m m' n n').
Proof. exact (MK_COMB (@lem7202692 R m n) (@lem7202691 R m m' n n')). Qed.
Lemma lem7202694 (R : type1626) (m : real) (m' : real) (n : real) : (term637 R m m' n) = (term638 R m m' n).
Proof. exact (fun_ext (fun n' : real => @lem7202693 R m m' n n')). Qed.
Lemma lem7202695 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7202696 (R : type1626) (m : real) (m' : real) (n : real) : (term629 R m m' n) = (term639 R m m' n).
Proof. exact (MK_COMB (@lem7202695) (@lem7202694 R m m' n)). Qed.
Lemma lem7202697 (R : type1626) (m : real) (m' : real) (n : real) : ((term628 R m m' n) = (term629 R m m' n)) = ((term624 R m m' n) = (term639 R m m' n)).
Proof. exact (MK_COMB (@lem7202690 R m m' n) (@lem7202696 R m m' n)). Qed.
Lemma lem7202698 (R : type1626) (m : real) (m' : real) (n : real) : (term624 R m m' n) = (term639 R m m' n).
Proof. exact (EQ_MP (@lem7202697 R m m' n) (@lem7202682 R m m' n)). Qed.
Lemma lem7202699 (R : type1626) (m : real) (n : real) : (term626 R m n) = (term640 R m n).
Proof. exact (fun_ext (fun m' : real => @lem7202698 R m m' n)). Qed.
Lemma lem7202700 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7202701 (R : type1626) (m : real) (n : real) : (term627 R m n) = (term641 R m n).
Proof. exact (MK_COMB (@lem7202700) (@lem7202699 R m n)). Qed.
Lemma lem7202702 (R : type1626) (m : real) (n : real) : (term530 R m n) = (term641 R m n).
Proof. exact (TRANS (@lem7202678 R m n) (@lem7202701 R m n)). Qed.
Lemma lem7202703 (R : type1626) (m : real) : (term531 R m) = (term642 R m).
Proof. exact (fun_ext (fun n : real => @lem7202702 R m n)). Qed.
Lemma lem7202704 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7202705 (R : type1626) (m : real) : (term532 R m) = (term643 R m).
Proof. exact (MK_COMB (@lem7202704) (@lem7202703 R m)). Qed.
Lemma lem7202706 (R : type1626) : (term533 R) = (term644 R).
Proof. exact (fun_ext (fun m : real => @lem7202705 R m)). Qed.
Lemma lem7202707 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7202708 (R : type1626) : (term534 R) = (term645 R).
Proof. exact (MK_COMB (@lem7202707) (@lem7202706 R)). Qed.
Lemma lem7202721 (R : type1626) (m : real) (m' : real) (n : real) (n' : real) : (term636 R m m' n n') = (term636 R m m' n n').
Proof. exact (eq_refl (term636 R m m' n n')). Qed.
Lemma lem7202722 (R : type1626) (m : real) (m' : real) (n : real) : (term638 R m m' n) = (term638 R m m' n).
Proof. exact (fun_ext (fun n' : real => @lem7202721 R m m' n n')). Qed.
Lemma lem7202723 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7202724 (R : type1626) (m : real) (m' : real) (n : real) : (term639 R m m' n) = (term639 R m m' n).
Proof. exact (MK_COMB (@lem7202723) (@lem7202722 R m m' n)). Qed.
Lemma lem7202725 (R : type1626) (m : real) (n : real) : (term640 R m n) = (term640 R m n).
Proof. exact (fun_ext (fun m' : real => @lem7202724 R m m' n)). Qed.
Lemma lem7202726 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7202727 (R : type1626) (m : real) (n : real) : (term641 R m n) = (term641 R m n).
Proof. exact (MK_COMB (@lem7202726) (@lem7202725 R m n)). Qed.
Lemma lem7202728 (R : type1626) (m : real) : (term642 R m) = (term642 R m).
Proof. exact (fun_ext (fun n : real => @lem7202727 R m n)). Qed.
Lemma lem7202729 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7202730 (R : type1626) (m : real) : (term643 R m) = (term643 R m).
Proof. exact (MK_COMB (@lem7202729) (@lem7202728 R m)). Qed.
Lemma lem7202731 (R : type1626) : (term644 R) = (term644 R).
Proof. exact (fun_ext (fun m : real => @lem7202730 R m)). Qed.
Lemma lem7202732 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7202733 (R : type1626) : (term645 R) = (term645 R).
Proof. exact (MK_COMB (@lem7202732) (@lem7202731 R)). Qed.
Lemma lem7202734 (R : type1626) : (term534 R) = (term645 R).
Proof. exact (TRANS (@lem7202708 R) (@lem7202733 R)). Qed.
Lemma lem7202735 (R : type1626) (h1 : term75 R) : term645 R.
Proof. exact (EQ_MP (@lem7202734 R) (@lem7202234 R h1)). Qed.
Lemma lem7202861 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (x : A) : (term546 A s R f g x) = (term546 A s R f g x).
Proof. exact (eq_refl (term546 A s R f g x)). Qed.
Lemma lem7202862 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term547 A s R f g) = (term547 A s R f g).
Proof. exact (fun_ext (fun x : A => @lem7202861 A s R f g x)). Qed.
Lemma lem7202863 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7202865 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) : (term548 A s R f g) = (term548 A s R f g).
Proof. exact (MK_COMB (@lem7202863 A) (@lem7202862 A s R f g)). Qed.
Lemma lem7202866 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (h1 : term80 A s R f g) : term548 A s R f g.
Proof. exact (EQ_MP (@lem7202865 A s R f g) (@lem7202299 A s R f g h1)). Qed.
Lemma lem7202872 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term554 A R f s g) = (term554 A R f s g).
Proof. exact (eq_refl (term554 A R f s g)). Qed.
Lemma lem7202889 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term588 A R x f g s) = (term646 A R x f g s).
Proof. exact (@lem19490 (term580 A x f g s) (term585 A s) (term573 A R x f g s)). Qed.
Lemma lem7202890 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7202891 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term590 A R x f g s) = (term647 A R x f g s).
Proof. exact (MK_COMB (@lem7202890) (@lem7202889 A R x f g s)). Qed.
Lemma lem7202892 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term592 A x R f s g) = (term648 A x R f s g).
Proof. exact (MK_COMB (@lem7202891 A R x f g s) (@lem7202872 A R f s g)). Qed.
Lemma lem7202899 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term648 A x R f s g) = (term649 A x R f s g).
Proof. exact (@lem19699 (term650 A x f g s) (term651 A R x f g s) (term554 A R f s g)). Qed.
Lemma lem7202900 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term592 A x R f s g) = (term649 A x R f s g).
Proof. exact (TRANS (@lem7202892 A x R f s g) (@lem7202899 A x R f s g)). Qed.
Lemma lem7202901 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (g : A -> real) : (term594 A x R f g) = (term652 A x R f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7202900 A x R f s g)). Qed.
Lemma lem7202902 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7202903 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (g : A -> real) : (term596 A x R f g) = (term653 A x R f g).
Proof. exact (MK_COMB (@lem7202902 A) (@lem7202901 A x R f g)). Qed.
Lemma lem7202904 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) : (term598 A x R f) = (term654 A x R f).
Proof. exact (fun_ext (fun g : A -> real => @lem7202903 A x R f g)). Qed.
Lemma lem7202905 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7202906 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) : (term599 A x R f) = (term655 A x R f).
Proof. exact (MK_COMB (@lem7202905 A) (@lem7202904 A x R f)). Qed.
Lemma lem7202907 {A : Type'} (x : type711 A) (R : type1626) : (term600 A x R) = (term656 A x R).
Proof. exact (fun_ext (fun f : A -> real => @lem7202906 A x R f)). Qed.
Lemma lem7202908 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7202910 {A : Type'} (x : type711 A) (R : type1626) : (term601 A x R) = (term657 A x R).
Proof. exact (MK_COMB (@lem7202908 A) (@lem7202907 A x R)). Qed.
Lemma lem7202911 {A : Type'} (x : type711 A) (R : type1626) (h1 : term601 A x R) : term657 A x R.
Proof. exact (EQ_MP (@lem7202910 A x R) (@lem7202650 A x R h1)). Qed.
Lemma lem7202912 (_96489 : real) (R : type1626) (h1 : term75 R) : term658 R _96489.
Proof. exact (@lem7202735 R h1 _96489). Qed.
Lemma lem7202913 (R : type1626) (_96489 : real) : (term658 R _96489) = (term643 R _96489).
Proof. exact (eq_refl (term658 R _96489)). Qed.
Lemma lem7202914 (_96489 : real) (R : type1626) (h1 : term75 R) : term643 R _96489.
Proof. exact (EQ_MP (@lem7202913 R _96489) (@lem7202912 _96489 R h1)). Qed.
Lemma lem7202915 (_96489 : real) (_96490 : real) (R : type1626) (h1 : term75 R) : term659 R _96489 _96490.
Proof. exact (@lem7202914 _96489 R h1 _96490). Qed.
Lemma lem7202916 (R : type1626) (_96489 : real) (_96490 : real) : (term659 R _96489 _96490) = (term641 R _96489 _96490).
Proof. exact (eq_refl (term659 R _96489 _96490)). Qed.
Lemma lem7202917 (_96489 : real) (_96490 : real) (R : type1626) (h1 : term75 R) : term641 R _96489 _96490.
Proof. exact (EQ_MP (@lem7202916 R _96489 _96490) (@lem7202915 _96489 _96490 R h1)). Qed.
Lemma lem7202918 (_96489 : real) (_96490 : real) (_96491 : real) (R : type1626) (h1 : term75 R) : term660 R _96489 _96490 _96491.
Proof. exact (@lem7202917 _96489 _96490 R h1 _96491). Qed.
Lemma lem7202919 (R : type1626) (_96489 : real) (_96491 : real) (_96490 : real) : (term660 R _96489 _96490 _96491) = (term639 R _96489 _96491 _96490).
Proof. exact (eq_refl (term660 R _96489 _96490 _96491)). Qed.
Lemma lem7202920 (_96489 : real) (_96491 : real) (_96490 : real) (R : type1626) (h1 : term75 R) : term639 R _96489 _96491 _96490.
Proof. exact (EQ_MP (@lem7202919 R _96489 _96491 _96490) (@lem7202918 _96489 _96490 _96491 R h1)). Qed.
Lemma lem7202921 (_96489 : real) (_96491 : real) (_96490 : real) (_96492 : real) (R : type1626) (h1 : term75 R) : term661 R _96489 _96491 _96490 _96492.
Proof. exact (@lem7202920 _96489 _96491 _96490 R h1 _96492). Qed.
Lemma lem7202922 (R : type1626) (_96489 : real) (_96491 : real) (_96490 : real) (_96492 : real) : (term661 R _96489 _96491 _96490 _96492) = (term636 R _96489 _96491 _96490 _96492).
Proof. exact (eq_refl (term661 R _96489 _96491 _96490 _96492)). Qed.
Lemma lem7202939 {A : Type'} (_96498 : A) (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (h1 : term80 A s R f g) : term662 A s R f g _96498.
Proof. exact (@lem7202866 A s R f g h1 _96498). Qed.
Lemma lem7202940 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (_96498 : A) : (term662 A s R f g _96498) = (term546 A s R f g _96498).
Proof. exact (eq_refl (term662 A s R f g _96498)). Qed.
Lemma lem7202942 {A : Type'} (_96499 : A -> real) (x : type711 A) (R : type1626) (h1 : term601 A x R) : term663 A x R _96499.
Proof. exact (@lem7202911 A x R h1 _96499). Qed.
Lemma lem7202943 {A : Type'} (x : type711 A) (R : type1626) (_96499 : A -> real) : (term663 A x R _96499) = (term655 A x R _96499).
Proof. exact (eq_refl (term663 A x R _96499)). Qed.
Lemma lem7202944 {A : Type'} (_96499 : A -> real) (x : type711 A) (R : type1626) (h1 : term601 A x R) : term655 A x R _96499.
Proof. exact (EQ_MP (@lem7202943 A x R _96499) (@lem7202942 A _96499 x R h1)). Qed.
Lemma lem7202945 {A : Type'} (_96499 : A -> real) (_96500 : A -> real) (x : type711 A) (R : type1626) (h1 : term601 A x R) : term664 A x R _96499 _96500.
Proof. exact (@lem7202944 A _96499 x R h1 _96500). Qed.
Lemma lem7202946 {A : Type'} (x : type711 A) (R : type1626) (_96499 : A -> real) (_96500 : A -> real) : (term664 A x R _96499 _96500) = (term653 A x R _96499 _96500).
Proof. exact (eq_refl (term664 A x R _96499 _96500)). Qed.
Lemma lem7202947 {A : Type'} (_96499 : A -> real) (_96500 : A -> real) (x : type711 A) (R : type1626) (h1 : term601 A x R) : term653 A x R _96499 _96500.
Proof. exact (EQ_MP (@lem7202946 A x R _96499 _96500) (@lem7202945 A _96499 _96500 x R h1)). Qed.
Lemma lem7202948 {A : Type'} (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) (x : type711 A) (R : type1626) (h1 : term601 A x R) : term665 A x R _96499 _96500 _96501.
Proof. exact (@lem7202947 A _96499 _96500 x R h1 _96501). Qed.
Lemma lem7202949 {A : Type'} (x : type711 A) (R : type1626) (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) : (term665 A x R _96499 _96500 _96501) = (term649 A x R _96499 _96501 _96500).
Proof. exact (eq_refl (term665 A x R _96499 _96500 _96501)). Qed.
Lemma lem7202950 {A : Type'} (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) (x : type711 A) (R : type1626) (h1 : term601 A x R) : term649 A x R _96499 _96501 _96500.
Proof. exact (EQ_MP (@lem7202949 A x R _96499 _96501 _96500) (@lem7202948 A _96499 _96500 _96501 x R h1)). Qed.
Lemma lem7202951 {A : Type'} (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) (x : type711 A) (R : type1626) (h1 : term601 A x R) : term666 A x R _96499 _96501 _96500.
Proof. exact (proj2 (@lem7202950 A _96499 _96501 _96500 x R h1)). Qed.
Lemma lem7202952 {A : Type'} (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) (x : type711 A) (R : type1626) (h1 : term601 A x R) : term667 A x R _96499 _96501 _96500.
Proof. exact (proj1 (@lem7202950 A _96499 _96501 _96500 x R h1)). Qed.
Lemma lem7202964 (_96489 : real) (_96491 : real) (_96490 : real) (_96492 : real) (R : type1626) (h1 : term75 R) : term636 R _96489 _96491 _96490 _96492.
Proof. exact (EQ_MP (@lem7202922 R _96489 _96491 _96490 _96492) (@lem7202921 _96489 _96491 _96490 _96492 R h1)). Qed.
Lemma lem7202976 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term609 R x1 y1 x2 y2) : term603 R x1 y1 x2 y2.
Proof. exact (proj2 (@lem7202649 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7203000 {A : Type'} (_96498 : A) (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (h1 : term80 A s R f g) : term546 A s R f g _96498.
Proof. exact (EQ_MP (@lem7202940 A s R f g _96498) (@lem7202939 A _96498 s R f g h1)). Qed.
Lemma lem7203002 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term239 A R f s g) : term555 A R f s g.
Proof. exact (EQ_MP (@lem7202350 A R f s g) (@lem7202077 A R f s g h1)). Qed.
Lemma lem7203013 {A : Type'} (x : type711 A) (R : type1626) (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) : (term667 A x R _96499 _96501 _96500) = (term668 A x R _96499 _96501 _96500).
Proof. exact (@lem7199898 (term585 A _96501) (term580 A x _96499 _96500 _96501) (term554 A R _96499 _96501 _96500)). Qed.
Lemma lem7203014 {A : Type'} (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) (x : type711 A) (R : type1626) (h1 : term601 A x R) : term668 A x R _96499 _96501 _96500.
Proof. exact (EQ_MP (@lem7203013 A x R _96499 _96501 _96500) (@lem7202952 A _96499 _96501 _96500 x R h1)). Qed.
Lemma lem7203025 {A : Type'} (x : type711 A) (R : type1626) (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) : (term666 A x R _96499 _96501 _96500) = (term669 A x R _96499 _96501 _96500).
Proof. exact (@lem7199898 (term585 A _96501) (term573 A R x _96499 _96500 _96501) (term554 A R _96499 _96501 _96500)). Qed.
Lemma lem7203026 {A : Type'} (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) (x : type711 A) (R : type1626) (h1 : term601 A x R) : term669 A x R _96499 _96501 _96500.
Proof. exact (EQ_MP (@lem7203025 A x R _96499 _96501 _96500) (@lem7202951 A _96499 _96501 _96500 x R h1)). Qed.
Lemma lem7203028 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term609 R x1 y1 x2 y2) : term521 R x1 x2.
Proof. exact (proj1 (@lem7202652 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7203029 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term609 R x1 y1 x2 y2) : term670 R x1 x2.
Proof. exact (fun h0 : term523 R x1 x2 => @lem7203028 R x1 y1 x2 y2 h1). Qed.
Lemma lem7203031 (p : Prop) : (term671 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7203032 (R : type1626) (x1 : real) (x2 : real) : (term670 R x1 x2) = (term521 R x1 x2).
Proof. exact (@lem7203031 (term521 R x1 x2)). Qed.
Lemma lem7203033 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term609 R x1 y1 x2 y2) : term521 R x1 x2.
Proof. exact (EQ_MP (@lem7203032 R x1 x2) (@lem7203029 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7203035 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term609 R x1 y1 x2 y2) : term521 R y1 y2.
Proof. exact (proj2 (@lem7202652 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7203036 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term609 R x1 y1 x2 y2) : term670 R y1 y2.
Proof. exact (fun h0 : term523 R y1 y2 => @lem7203035 R x1 y1 x2 y2 h1). Qed.
Lemma lem7203038 (p : Prop) : (term671 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7203039 (R : type1626) (y1 : real) (y2 : real) : (term670 R y1 y2) = (term521 R y1 y2).
Proof. exact (@lem7203038 (term521 R y1 y2)). Qed.
Lemma lem7203040 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term609 R x1 y1 x2 y2) : term521 R y1 y2.
Proof. exact (EQ_MP (@lem7203039 R y1 y2) (@lem7203036 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7203056 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7203057 (_96489 : real) (_96490 : real) (R : type1626) (_96491 : real) (_96492 : real) : (term525 R _96489 _96491 _96490 _96492) = (term672 _96489 _96490 R _96491 _96492).
Proof. exact (@lem7203056 (term520 R _96489 _96491 _96490 _96492) (term523 R _96491 _96492)). Qed.
Lemma lem7203063 (R : type1626) (_96489 : real) (_96490 : real) : (term524 R _96489 _96490) = (term524 R _96489 _96490).
Proof. exact (eq_refl (term524 R _96489 _96490)). Qed.
Lemma lem7203064 (_96489 : real) (_96490 : real) (R : type1626) (_96491 : real) (_96492 : real) : (term636 R _96489 _96491 _96490 _96492) = (term673 _96489 _96490 R _96491 _96492).
Proof. exact (MK_COMB (@lem7203063 R _96489 _96490) (@lem7203057 _96489 _96490 R _96491 _96492)). Qed.
Lemma lem7203068 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7203069 (_96489 : real) (_96490 : real) (R : type1626) (_96491 : real) (_96492 : real) : (term673 _96489 _96490 R _96491 _96492) = (term674 _96489 _96490 R _96491 _96492).
Proof. exact (@lem7203068 (term520 R _96489 _96491 _96490 _96492) (term523 R _96489 _96490) (term523 R _96491 _96492)). Qed.
Lemma lem7203085 (_96489 : real) (_96490 : real) (R : type1626) (_96491 : real) (_96492 : real) : (term636 R _96489 _96491 _96490 _96492) = (term674 _96489 _96490 R _96491 _96492).
Proof. exact (TRANS (@lem7203064 _96489 _96490 R _96491 _96492) (@lem7203069 _96489 _96490 R _96491 _96492)). Qed.
Lemma lem7203086 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7203087 (_96489 : real) (_96490 : real) (R : type1626) (_96491 : real) (_96492 : real) : (term675 R _96489 _96491 _96490 _96492) = (term676 _96489 _96490 R _96491 _96492).
Proof. exact (MK_COMB (@lem7203086) (@lem7203085 _96489 _96490 R _96491 _96492)). Qed.
Lemma lem7203103 (_96489 : real) (_96490 : real) (R : type1626) (_96491 : real) (_96492 : real) : (term674 _96489 _96490 R _96491 _96492) = (term674 _96489 _96490 R _96491 _96492).
Proof. exact (eq_refl (term674 _96489 _96490 R _96491 _96492)). Qed.
Lemma lem7203104 (_96489 : real) (_96490 : real) (R : type1626) (_96491 : real) (_96492 : real) : ((term636 R _96489 _96491 _96490 _96492) = (term674 _96489 _96490 R _96491 _96492)) = ((term674 _96489 _96490 R _96491 _96492) = (term674 _96489 _96490 R _96491 _96492)).
Proof. exact (MK_COMB (@lem7203087 _96489 _96490 R _96491 _96492) (@lem7203103 _96489 _96490 R _96491 _96492)). Qed.
Lemma lem7203106 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7203107 (x : Prop) : (x = x) = True.
Proof. exact (@lem7203106 Prop x). Qed.
Lemma lem7203108 (_96489 : real) (_96490 : real) (R : type1626) (_96491 : real) (_96492 : real) : ((term674 _96489 _96490 R _96491 _96492) = (term674 _96489 _96490 R _96491 _96492)) = True.
Proof. exact (@lem7203107 (term674 _96489 _96490 R _96491 _96492)). Qed.
Lemma lem7203109 (_96489 : real) (_96490 : real) (R : type1626) (_96491 : real) (_96492 : real) : ((term636 R _96489 _96491 _96490 _96492) = (term674 _96489 _96490 R _96491 _96492)) = True.
Proof. exact (TRANS (@lem7203104 _96489 _96490 R _96491 _96492) (@lem7203108 _96489 _96490 R _96491 _96492)). Qed.
Lemma lem7203110 (_96489 : real) (_96490 : real) (R : type1626) (_96491 : real) (_96492 : real) : True = ((term636 R _96489 _96491 _96490 _96492) = (term674 _96489 _96490 R _96491 _96492)).
Proof. exact (SYM (@lem7203109 _96489 _96490 R _96491 _96492)). Qed.
Lemma lem7203111 (_96489 : real) (_96490 : real) (R : type1626) (_96491 : real) (_96492 : real) : (term636 R _96489 _96491 _96490 _96492) = (term674 _96489 _96490 R _96491 _96492).
Proof. exact (EQ_MP (@lem7203110 _96489 _96490 R _96491 _96492) (@lem0)). Qed.
Lemma lem7203112 (_96489 : real) (_96490 : real) (_96491 : real) (_96492 : real) (R : type1626) (h1 : term75 R) : term674 _96489 _96490 R _96491 _96492.
Proof. exact (EQ_MP (@lem7203111 _96489 _96490 R _96491 _96492) (@lem7202964 _96489 _96491 _96490 _96492 R h1)). Qed.
Lemma lem7203114 (b : Prop) (a : Prop) : (a \/ b) = (term677 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7203115 (R : type1626) (_96489 : real) (_96491 : real) (_96490 : real) (_96492 : real) : (term674 _96489 _96490 R _96491 _96492) = (term678 R _96489 _96491 _96490 _96492).
Proof. exact (@lem7203114 (term679 _96489 _96490 R _96491 _96492) (term520 R _96489 _96491 _96490 _96492)). Qed.
Lemma lem7203117 (a : Prop) (b : Prop) : (term680 a b) = (term681 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7203118 (_96489 : real) (_96490 : real) (R : type1626) (_96491 : real) (_96492 : real) : (term682 _96489 _96490 R _96491 _96492) = (term683 _96489 _96490 R _96491 _96492).
Proof. exact (@lem7203117 (term523 R _96489 _96490) (term523 R _96491 _96492)). Qed.
Lemma lem7203120 (a : Prop) : (term219 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7203121 (R : type1626) (_96489 : real) (_96490 : real) : (term684 R _96489 _96490) = (term521 R _96489 _96490).
Proof. exact (@lem7203120 (term521 R _96489 _96490)). Qed.
Lemma lem7203122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7203123 (R : type1626) (_96489 : real) (_96490 : real) : (term685 R _96489 _96490) = (term605 R _96489 _96490).
Proof. exact (MK_COMB (@lem7203122) (@lem7203121 R _96489 _96490)). Qed.
Lemma lem7203125 (a : Prop) : (term219 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7203126 (R : type1626) (_96491 : real) (_96492 : real) : (term684 R _96491 _96492) = (term521 R _96491 _96492).
Proof. exact (@lem7203125 (term521 R _96491 _96492)). Qed.
Lemma lem7203127 (_96489 : real) (_96490 : real) (R : type1626) (_96491 : real) (_96492 : real) : (term683 _96489 _96490 R _96491 _96492) = (term606 _96489 _96490 R _96491 _96492).
Proof. exact (MK_COMB (@lem7203123 R _96489 _96490) (@lem7203126 R _96491 _96492)). Qed.
Lemma lem7203128 (_96489 : real) (_96490 : real) (R : type1626) (_96491 : real) (_96492 : real) : (term682 _96489 _96490 R _96491 _96492) = (term606 _96489 _96490 R _96491 _96492).
Proof. exact (TRANS (@lem7203118 _96489 _96490 R _96491 _96492) (@lem7203127 _96489 _96490 R _96491 _96492)). Qed.
Lemma lem7203129 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7203130 (_96489 : real) (_96490 : real) (R : type1626) (_96491 : real) (_96492 : real) : (term686 _96489 _96490 R _96491 _96492) = (term687 _96489 _96490 R _96491 _96492).
Proof. exact (MK_COMB (@lem7203129) (@lem7203128 _96489 _96490 R _96491 _96492)). Qed.
Lemma lem7203131 (R : type1626) (_96489 : real) (_96491 : real) (_96490 : real) (_96492 : real) : (term520 R _96489 _96491 _96490 _96492) = (term520 R _96489 _96491 _96490 _96492).
Proof. exact (eq_refl (term520 R _96489 _96491 _96490 _96492)). Qed.
Lemma lem7203132 (R : type1626) (_96489 : real) (_96491 : real) (_96490 : real) (_96492 : real) : (term678 R _96489 _96491 _96490 _96492) = (term688 R _96489 _96491 _96490 _96492).
Proof. exact (MK_COMB (@lem7203130 _96489 _96490 R _96491 _96492) (@lem7203131 R _96489 _96491 _96490 _96492)). Qed.
Lemma lem7203133 (R : type1626) (_96489 : real) (_96491 : real) (_96490 : real) (_96492 : real) : (term674 _96489 _96490 R _96491 _96492) = (term688 R _96489 _96491 _96490 _96492).
Proof. exact (TRANS (@lem7203115 R _96489 _96491 _96490 _96492) (@lem7203132 R _96489 _96491 _96490 _96492)). Qed.
Lemma lem7203135 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term609 R x1 y1 x2 y2) : term606 x1 x2 R y1 y2.
Proof. exact (conj (@lem7203033 R x1 y1 x2 y2 h1) (@lem7203040 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7203137 (_96489 : real) (_96491 : real) (_96490 : real) (_96492 : real) (R : type1626) (h1 : term75 R) : term688 R _96489 _96491 _96490 _96492.
Proof. exact (EQ_MP (@lem7203133 R _96489 _96491 _96490 _96492) (@lem7203112 _96489 _96490 _96491 _96492 R h1)). Qed.
Lemma lem7203138 (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) (h1 : term75 R) : term688 R x1 y1 x2 y2.
Proof. exact (@lem7203137 x1 y1 x2 y2 R h1). Qed.
Lemma lem7203141 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term75 R) (h2 : term609 R x1 y1 x2 y2) : term520 R x1 y1 x2 y2.
Proof. exact (@lem7203138 x1 y1 x2 y2 R h1 (@lem7203135 R x1 y1 x2 y2 h2)). Qed.
Lemma lem7203142 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term75 R) (h2 : term609 R x1 y1 x2 y2) : term689 R x1 y1 x2 y2.
Proof. exact (fun h0 : term603 R x1 y1 x2 y2 => @lem7203141 R x1 y1 x2 y2 h1 h2). Qed.
Lemma lem7203144 (p : Prop) : (term671 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7203145 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term689 R x1 y1 x2 y2) = (term520 R x1 y1 x2 y2).
Proof. exact (@lem7203144 (term520 R x1 y1 x2 y2)). Qed.
Lemma lem7203146 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term75 R) (h2 : term609 R x1 y1 x2 y2) : term520 R x1 y1 x2 y2.
Proof. exact (EQ_MP (@lem7203145 R x1 y1 x2 y2) (@lem7203142 R x1 y1 x2 y2 h1 h2)). Qed.
Lemma lem7203149 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7203151 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term603 R x1 y1 x2 y2) = (term690 R x1 y1 x2 y2).
Proof. exact (@lem7203149 (term520 R x1 y1 x2 y2)). Qed.
Lemma lem7203154 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term609 R x1 y1 x2 y2) : term690 R x1 y1 x2 y2.
Proof. exact (EQ_MP (@lem7203151 R x1 y1 x2 y2) (@lem7202976 R x1 y1 x2 y2 h1)). Qed.
Lemma lem7203157 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term75 R) (h2 : term609 R x1 y1 x2 y2) : False.
Proof. exact (@lem7203154 R x1 y1 x2 y2 h2 (@lem7203146 R x1 y1 x2 y2 h1 h2)). Qed.
Lemma lem7203158 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term75 R) (h2 : term609 R x1 y1 x2 y2) : term691.
Proof. exact (fun h0 : ~ False => @lem7203157 R x1 y1 x2 y2 h1 h2). Qed.
Lemma lem7203160 (p : Prop) : (term671 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7203161 : term691 = False.
Proof. exact (@lem7203160 False). Qed.
Lemma lem7203162 (R : type1626) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (h1 : term75 R) (h2 : term609 R x1 y1 x2 y2) : False.
Proof. exact (EQ_MP (@lem7203161) (@lem7203158 R x1 y1 x2 y2 h1 h2)). Qed.
Lemma lem7203164 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7202242 A s) (@lem7202008 A s h1)). Qed.
Lemma lem7203165 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term692 A s.
Proof. exact (fun h0 : term585 A s => @lem7203164 A s h1). Qed.
Lemma lem7203167 (p : Prop) : (term671 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7203168 {A : Type'} (s : A -> Prop) : (term692 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7203167 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem7203169 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7203168 A s) (@lem7203165 A s h1)). Qed.
Lemma lem7203171 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7202242 A s) (@lem7202008 A s h1)). Qed.
Lemma lem7203172 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term692 A s.
Proof. exact (fun h0 : term585 A s => @lem7203171 A s h1). Qed.
Lemma lem7203174 (p : Prop) : (term671 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7203175 {A : Type'} (s : A -> Prop) : (term692 A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7203174 (@I ((A -> Prop) -> Prop) (@FINITE A) s)). Qed.
Lemma lem7203176 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @I ((A -> Prop) -> Prop) (@FINITE A) s.
Proof. exact (EQ_MP (@lem7203175 A s) (@lem7203172 A s h1)). Qed.
Lemma lem7203179 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term555 A R f s g) : term555 A R f s g.
Proof. exact (h1). Qed.
Lemma lem7203180 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term555 A R f s g) : term693 A R f s g.
Proof. exact (fun h0 : term554 A R f s g => @lem7203179 A R f s g h1). Qed.
Lemma lem7203182 (p : Prop) : (term694 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7203183 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term693 A R f s g) = (term555 A R f s g).
Proof. exact (@lem7203182 (term554 A R f s g)). Qed.
Lemma lem7203184 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term555 A R f s g) : term555 A R f s g.
Proof. exact (EQ_MP (@lem7203183 A R f s g) (@lem7203180 A R f s g h1)). Qed.
Lemma lem7203190 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7203191 {A : Type'} (x : type711 A) (R : type1626) (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) : (term668 A x R _96499 _96501 _96500) = (term695 A x R _96499 _96501 _96500).
Proof. exact (@lem7203190 (term580 A x _96499 _96500 _96501) (term585 A _96501) (term554 A R _96499 _96501 _96500)). Qed.
Lemma lem7203205 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7203206 {A : Type'} (R : type1626) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term696 A R _96499 _96501 _96500) = (term697 A R _96499 _96500 _96501).
Proof. exact (@lem7203205 (term554 A R _96499 _96501 _96500) (term585 A _96501)). Qed.
Lemma lem7203212 {A : Type'} (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term698 A x _96499 _96500 _96501) = (term698 A x _96499 _96500 _96501).
Proof. exact (eq_refl (term698 A x _96499 _96500 _96501)). Qed.
Lemma lem7203213 {A : Type'} (x : type711 A) (R : type1626) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term695 A x R _96499 _96501 _96500) = (term699 A x R _96499 _96500 _96501).
Proof. exact (MK_COMB (@lem7203212 A x _96499 _96500 _96501) (@lem7203206 A R _96499 _96500 _96501)). Qed.
Lemma lem7203224 {A : Type'} (x : type711 A) (R : type1626) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term668 A x R _96499 _96501 _96500) = (term699 A x R _96499 _96500 _96501).
Proof. exact (TRANS (@lem7203191 A x R _96499 _96501 _96500) (@lem7203213 A x R _96499 _96500 _96501)). Qed.
Lemma lem7203225 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7203226 {A : Type'} (x : type711 A) (R : type1626) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term700 A x R _96499 _96501 _96500) = (term701 A x R _96499 _96500 _96501).
Proof. exact (MK_COMB (@lem7203225) (@lem7203224 A x R _96499 _96500 _96501)). Qed.
Lemma lem7203240 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7203241 {A : Type'} (R : type1626) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term696 A R _96499 _96501 _96500) = (term697 A R _96499 _96500 _96501).
Proof. exact (@lem7203240 (term554 A R _96499 _96501 _96500) (term585 A _96501)). Qed.
Lemma lem7203247 {A : Type'} (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term698 A x _96499 _96500 _96501) = (term698 A x _96499 _96500 _96501).
Proof. exact (eq_refl (term698 A x _96499 _96500 _96501)). Qed.
Lemma lem7203248 {A : Type'} (x : type711 A) (R : type1626) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term695 A x R _96499 _96501 _96500) = (term699 A x R _96499 _96500 _96501).
Proof. exact (MK_COMB (@lem7203247 A x _96499 _96500 _96501) (@lem7203241 A R _96499 _96500 _96501)). Qed.
Lemma lem7203259 {A : Type'} (x : type711 A) (R : type1626) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : ((term668 A x R _96499 _96501 _96500) = (term695 A x R _96499 _96501 _96500)) = ((term699 A x R _96499 _96500 _96501) = (term699 A x R _96499 _96500 _96501)).
Proof. exact (MK_COMB (@lem7203226 A x R _96499 _96500 _96501) (@lem7203248 A x R _96499 _96500 _96501)). Qed.
Lemma lem7203261 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7203262 (x : Prop) : (x = x) = True.
Proof. exact (@lem7203261 Prop x). Qed.
Lemma lem7203263 {A : Type'} (x : type711 A) (R : type1626) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : ((term699 A x R _96499 _96500 _96501) = (term699 A x R _96499 _96500 _96501)) = True.
Proof. exact (@lem7203262 (term699 A x R _96499 _96500 _96501)). Qed.
Lemma lem7203264 {A : Type'} (x : type711 A) (R : type1626) (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) : ((term668 A x R _96499 _96501 _96500) = (term695 A x R _96499 _96501 _96500)) = True.
Proof. exact (TRANS (@lem7203259 A x R _96499 _96500 _96501) (@lem7203263 A x R _96499 _96500 _96501)). Qed.
Lemma lem7203265 {A : Type'} (x : type711 A) (R : type1626) (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) : True = ((term668 A x R _96499 _96501 _96500) = (term695 A x R _96499 _96501 _96500)).
Proof. exact (SYM (@lem7203264 A x R _96499 _96501 _96500)). Qed.
Lemma lem7203266 {A : Type'} (x : type711 A) (R : type1626) (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) : (term668 A x R _96499 _96501 _96500) = (term695 A x R _96499 _96501 _96500).
Proof. exact (EQ_MP (@lem7203265 A x R _96499 _96501 _96500) (@lem0)). Qed.
Lemma lem7203267 {A : Type'} (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) (x : type711 A) (R : type1626) (h1 : term601 A x R) : term695 A x R _96499 _96501 _96500.
Proof. exact (EQ_MP (@lem7203266 A x R _96499 _96501 _96500) (@lem7203014 A _96499 _96501 _96500 x R h1)). Qed.
Lemma lem7203269 (b : Prop) (a : Prop) : (a \/ b) = (term677 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7203270 {A : Type'} (R : type1626) (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term695 A x R _96499 _96501 _96500) = (term702 A R x _96499 _96500 _96501).
Proof. exact (@lem7203269 (term696 A R _96499 _96501 _96500) (term580 A x _96499 _96500 _96501)). Qed.
Lemma lem7203272 (a : Prop) (b : Prop) : (term680 a b) = (term681 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7203273 {A : Type'} (R : type1626) (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) : (term703 A R _96499 _96501 _96500) = (term704 A R _96499 _96501 _96500).
Proof. exact (@lem7203272 (term585 A _96501) (term554 A R _96499 _96501 _96500)). Qed.
Lemma lem7203275 (a : Prop) : (term219 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7203276 {A : Type'} (_96501 : A -> Prop) : (term705 A _96501) = (@I ((A -> Prop) -> Prop) (@FINITE A) _96501).
Proof. exact (@lem7203275 (@I ((A -> Prop) -> Prop) (@FINITE A) _96501)). Qed.
Lemma lem7203277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7203278 {A : Type'} (_96501 : A -> Prop) : (term706 A _96501) = (term707 A _96501).
Proof. exact (MK_COMB (@lem7203277) (@lem7203276 A _96501)). Qed.
Lemma lem7203279 {A : Type'} (R : type1626) (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) : (term555 A R _96499 _96501 _96500) = (term555 A R _96499 _96501 _96500).
Proof. exact (eq_refl (term555 A R _96499 _96501 _96500)). Qed.
Lemma lem7203280 {A : Type'} (R : type1626) (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) : (term704 A R _96499 _96501 _96500) = (term708 A R _96499 _96501 _96500).
Proof. exact (MK_COMB (@lem7203278 A _96501) (@lem7203279 A R _96499 _96501 _96500)). Qed.
Lemma lem7203281 {A : Type'} (R : type1626) (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) : (term703 A R _96499 _96501 _96500) = (term708 A R _96499 _96501 _96500).
Proof. exact (TRANS (@lem7203273 A R _96499 _96501 _96500) (@lem7203280 A R _96499 _96501 _96500)). Qed.
Lemma lem7203282 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7203283 {A : Type'} (R : type1626) (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) : (term709 A R _96499 _96501 _96500) = (term710 A R _96499 _96501 _96500).
Proof. exact (MK_COMB (@lem7203282) (@lem7203281 A R _96499 _96501 _96500)). Qed.
Lemma lem7203284 {A : Type'} (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term580 A x _96499 _96500 _96501) = (term580 A x _96499 _96500 _96501).
Proof. exact (eq_refl (term580 A x _96499 _96500 _96501)). Qed.
Lemma lem7203285 {A : Type'} (R : type1626) (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term702 A R x _96499 _96500 _96501) = (term711 A R x _96499 _96500 _96501).
Proof. exact (MK_COMB (@lem7203283 A R _96499 _96501 _96500) (@lem7203284 A x _96499 _96500 _96501)). Qed.
Lemma lem7203286 {A : Type'} (R : type1626) (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term695 A x R _96499 _96501 _96500) = (term711 A R x _96499 _96500 _96501).
Proof. exact (TRANS (@lem7203270 A R x _96499 _96500 _96501) (@lem7203285 A R x _96499 _96500 _96501)). Qed.
Lemma lem7203288 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : @FINITE A s) (h2 : term555 A R f s g) : term708 A R f s g.
Proof. exact (conj (@lem7203176 A s h1) (@lem7203184 A R f s g h2)). Qed.
Lemma lem7203290 {A : Type'} (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) (x : type711 A) (R : type1626) (h1 : term601 A x R) : term711 A R x _96499 _96500 _96501.
Proof. exact (EQ_MP (@lem7203286 A R x _96499 _96500 _96501) (@lem7203267 A _96499 _96501 _96500 x R h1)). Qed.
Lemma lem7203291 {A : Type'} (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) (x : type711 A) (R : type1626) (h1 : term601 A x R) : term711 A R x _96499 _96500 _96501.
Proof. exact (@lem7203290 A _96499 _96500 _96501 x R h1). Qed.
Lemma lem7203292 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (x : type711 A) (R : type1626) (h1 : term601 A x R) : term711 A R x f g s.
Proof. exact (@lem7203291 A f g s x R h1). Qed.
Lemma lem7203295 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term601 A x R) (h2 : @FINITE A s) (h3 : term555 A R f s g) : term580 A x f g s.
Proof. exact (@lem7203292 A f g s x R h1 (@lem7203288 A R f s g h2 h3)). Qed.
Lemma lem7203296 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term601 A x R) (h2 : @FINITE A s) (h3 : term555 A R f s g) : term712 A x f g s.
Proof. exact (fun h0 : term713 A x f g s => @lem7203295 A x R f s g h1 h2 h3). Qed.
Lemma lem7203298 (p : Prop) : (term671 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7203299 {A : Type'} (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term712 A x f g s) = (term580 A x f g s).
Proof. exact (@lem7203298 (term580 A x f g s)). Qed.
Lemma lem7203300 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term601 A x R) (h2 : @FINITE A s) (h3 : term555 A R f s g) : term580 A x f g s.
Proof. exact (EQ_MP (@lem7203299 A x f g s) (@lem7203296 A x R f s g h1 h2 h3)). Qed.
Lemma lem7203306 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7203307 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (_96498 : A) (s : A -> Prop) : (term546 A s R f g _96498) = (term714 A R f g _96498 s).
Proof. exact (@lem7203306 (term540 A R f g _96498) (term543 A _96498 s)). Qed.
Lemma lem7203313 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7203314 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (_96498 : A) (s : A -> Prop) : (term715 A s R f g _96498) = (term716 A R f g _96498 s).
Proof. exact (MK_COMB (@lem7203313) (@lem7203307 A R f g _96498 s)). Qed.
Lemma lem7203320 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (_96498 : A) (s : A -> Prop) : (term714 A R f g _96498 s) = (term714 A R f g _96498 s).
Proof. exact (eq_refl (term714 A R f g _96498 s)). Qed.
Lemma lem7203321 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (_96498 : A) (s : A -> Prop) : ((term546 A s R f g _96498) = (term714 A R f g _96498 s)) = ((term714 A R f g _96498 s) = (term714 A R f g _96498 s)).
Proof. exact (MK_COMB (@lem7203314 A R f g _96498 s) (@lem7203320 A R f g _96498 s)). Qed.
Lemma lem7203323 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7203324 (x : Prop) : (x = x) = True.
Proof. exact (@lem7203323 Prop x). Qed.
Lemma lem7203325 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (_96498 : A) (s : A -> Prop) : ((term714 A R f g _96498 s) = (term714 A R f g _96498 s)) = True.
Proof. exact (@lem7203324 (term714 A R f g _96498 s)). Qed.
Lemma lem7203326 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (_96498 : A) (s : A -> Prop) : ((term546 A s R f g _96498) = (term714 A R f g _96498 s)) = True.
Proof. exact (TRANS (@lem7203321 A R f g _96498 s) (@lem7203325 A R f g _96498 s)). Qed.
Lemma lem7203327 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (_96498 : A) (s : A -> Prop) : True = ((term546 A s R f g _96498) = (term714 A R f g _96498 s)).
Proof. exact (SYM (@lem7203326 A R f g _96498 s)). Qed.
Lemma lem7203328 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (_96498 : A) (s : A -> Prop) : (term546 A s R f g _96498) = (term714 A R f g _96498 s).
Proof. exact (EQ_MP (@lem7203327 A R f g _96498 s) (@lem0)). Qed.
Lemma lem7203329 {A : Type'} (_96498 : A) (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (h1 : term80 A s R f g) : term714 A R f g _96498 s.
Proof. exact (EQ_MP (@lem7203328 A R f g _96498 s) (@lem7203000 A _96498 s R f g h1)). Qed.
Lemma lem7203331 (b : Prop) (a : Prop) : (a \/ b) = (term677 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7203332 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (_96498 : A) : (term714 A R f g _96498 s) = (term717 A s R f g _96498).
Proof. exact (@lem7203331 (term543 A _96498 s) (term540 A R f g _96498)). Qed.
Lemma lem7203334 (a : Prop) : (term219 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7203335 {A : Type'} (_96498 : A) (s : A -> Prop) : (term718 A _96498 s) = (term541 A _96498 s).
Proof. exact (@lem7203334 (term541 A _96498 s)). Qed.
Lemma lem7203336 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7203337 {A : Type'} (_96498 : A) (s : A -> Prop) : (term719 A _96498 s) = (term720 A _96498 s).
Proof. exact (MK_COMB (@lem7203336) (@lem7203335 A _96498 s)). Qed.
Lemma lem7203338 {A : Type'} (R : type1626) (f : A -> real) (g : A -> real) (_96498 : A) : (term540 A R f g _96498) = (term540 A R f g _96498).
Proof. exact (eq_refl (term540 A R f g _96498)). Qed.
Lemma lem7203339 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (_96498 : A) : (term717 A s R f g _96498) = (term721 A s R f g _96498).
Proof. exact (MK_COMB (@lem7203337 A _96498 s) (@lem7203338 A R f g _96498)). Qed.
Lemma lem7203340 {A : Type'} (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (_96498 : A) : (term714 A R f g _96498 s) = (term721 A s R f g _96498).
Proof. exact (TRANS (@lem7203332 A s R f g _96498) (@lem7203339 A s R f g _96498)). Qed.
Lemma lem7203343 {A : Type'} (_96498 : A) (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (h1 : term80 A s R f g) : term721 A s R f g _96498.
Proof. exact (EQ_MP (@lem7203340 A s R f g _96498) (@lem7203329 A _96498 s R f g h1)). Qed.
Lemma lem7203344 {A : Type'} (_96498 : A) (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (h1 : term80 A s R f g) : term721 A s R f g _96498.
Proof. exact (@lem7203343 A _96498 s R f g h1). Qed.
Lemma lem7203345 {A : Type'} (x : type711 A) (s : A -> Prop) (R : type1626) (f : A -> real) (g : A -> real) (h1 : term80 A s R f g) : term722 A R x f g s.
Proof. exact (@lem7203344 A (term558 A x f g s) s R f g h1). Qed.
Lemma lem7203348 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term601 A x R) (h3 : @FINITE A s) (h4 : term555 A R f s g) : term571 A R x f g s.
Proof. exact (@lem7203345 A x s R f g h1 (@lem7203300 A x R f s g h2 h3 h4)). Qed.
Lemma lem7203349 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term601 A x R) (h3 : @FINITE A s) (h4 : term555 A R f s g) : term723 A R x f g s.
Proof. exact (fun h0 : term573 A R x f g s => @lem7203348 A x R f s g h1 h2 h3 h4). Qed.
Lemma lem7203351 (p : Prop) : (term671 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7203352 {A : Type'} (R : type1626) (x : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term723 A R x f g s) = (term571 A R x f g s).
Proof. exact (@lem7203351 (term571 A R x f g s)). Qed.
Lemma lem7203353 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term601 A x R) (h3 : @FINITE A s) (h4 : term555 A R f s g) : term571 A R x f g s.
Proof. exact (EQ_MP (@lem7203352 A R x f g s) (@lem7203349 A x R f s g h1 h2 h3 h4)). Qed.
Lemma lem7203369 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7203370 {A : Type'} (R : type1626) (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term724 A x R _96499 _96501 _96500) = (term725 A R x _96499 _96500 _96501).
Proof. exact (@lem7203369 (term554 A R _96499 _96501 _96500) (term573 A R x _96499 _96500 _96501)). Qed.
Lemma lem7203376 {A : Type'} (_96501 : A -> Prop) : (term586 A _96501) = (term586 A _96501).
Proof. exact (eq_refl (term586 A _96501)). Qed.
Lemma lem7203377 {A : Type'} (R : type1626) (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term669 A x R _96499 _96501 _96500) = (term726 A R x _96499 _96500 _96501).
Proof. exact (MK_COMB (@lem7203376 A _96501) (@lem7203370 A R x _96499 _96500 _96501)). Qed.
Lemma lem7203381 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7203382 {A : Type'} (R : type1626) (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term726 A R x _96499 _96500 _96501) = (term727 A R x _96499 _96500 _96501).
Proof. exact (@lem7203381 (term554 A R _96499 _96501 _96500) (term585 A _96501) (term573 A R x _96499 _96500 _96501)). Qed.
Lemma lem7203398 {A : Type'} (R : type1626) (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term669 A x R _96499 _96501 _96500) = (term727 A R x _96499 _96500 _96501).
Proof. exact (TRANS (@lem7203377 A R x _96499 _96500 _96501) (@lem7203382 A R x _96499 _96500 _96501)). Qed.
Lemma lem7203399 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7203400 {A : Type'} (R : type1626) (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term728 A x R _96499 _96501 _96500) = (term729 A R x _96499 _96500 _96501).
Proof. exact (MK_COMB (@lem7203399) (@lem7203398 A R x _96499 _96500 _96501)). Qed.
Lemma lem7203416 {A : Type'} (R : type1626) (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term727 A R x _96499 _96500 _96501) = (term727 A R x _96499 _96500 _96501).
Proof. exact (eq_refl (term727 A R x _96499 _96500 _96501)). Qed.
Lemma lem7203417 {A : Type'} (R : type1626) (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : ((term669 A x R _96499 _96501 _96500) = (term727 A R x _96499 _96500 _96501)) = ((term727 A R x _96499 _96500 _96501) = (term727 A R x _96499 _96500 _96501)).
Proof. exact (MK_COMB (@lem7203400 A R x _96499 _96500 _96501) (@lem7203416 A R x _96499 _96500 _96501)). Qed.
Lemma lem7203419 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7203420 (x : Prop) : (x = x) = True.
Proof. exact (@lem7203419 Prop x). Qed.
Lemma lem7203421 {A : Type'} (R : type1626) (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : ((term727 A R x _96499 _96500 _96501) = (term727 A R x _96499 _96500 _96501)) = True.
Proof. exact (@lem7203420 (term727 A R x _96499 _96500 _96501)). Qed.
Lemma lem7203422 {A : Type'} (R : type1626) (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : ((term669 A x R _96499 _96501 _96500) = (term727 A R x _96499 _96500 _96501)) = True.
Proof. exact (TRANS (@lem7203417 A R x _96499 _96500 _96501) (@lem7203421 A R x _96499 _96500 _96501)). Qed.
Lemma lem7203423 {A : Type'} (R : type1626) (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : True = ((term669 A x R _96499 _96501 _96500) = (term727 A R x _96499 _96500 _96501)).
Proof. exact (SYM (@lem7203422 A R x _96499 _96500 _96501)). Qed.
Lemma lem7203424 {A : Type'} (R : type1626) (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term669 A x R _96499 _96501 _96500) = (term727 A R x _96499 _96500 _96501).
Proof. exact (EQ_MP (@lem7203423 A R x _96499 _96500 _96501) (@lem0)). Qed.
Lemma lem7203425 {A : Type'} (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) (x : type711 A) (R : type1626) (h1 : term601 A x R) : term727 A R x _96499 _96500 _96501.
Proof. exact (EQ_MP (@lem7203424 A R x _96499 _96500 _96501) (@lem7203026 A _96499 _96501 _96500 x R h1)). Qed.
Lemma lem7203427 (b : Prop) (a : Prop) : (a \/ b) = (term677 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7203428 {A : Type'} (x : type711 A) (R : type1626) (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) : (term727 A R x _96499 _96500 _96501) = (term730 A x R _96499 _96501 _96500).
Proof. exact (@lem7203427 (term651 A R x _96499 _96500 _96501) (term554 A R _96499 _96501 _96500)). Qed.
Lemma lem7203430 (a : Prop) (b : Prop) : (term680 a b) = (term681 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7203431 {A : Type'} (R : type1626) (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term731 A R x _96499 _96500 _96501) = (term732 A R x _96499 _96500 _96501).
Proof. exact (@lem7203430 (term585 A _96501) (term573 A R x _96499 _96500 _96501)). Qed.
Lemma lem7203433 (a : Prop) : (term219 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7203434 {A : Type'} (_96501 : A -> Prop) : (term705 A _96501) = (@I ((A -> Prop) -> Prop) (@FINITE A) _96501).
Proof. exact (@lem7203433 (@I ((A -> Prop) -> Prop) (@FINITE A) _96501)). Qed.
Lemma lem7203435 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7203436 {A : Type'} (_96501 : A -> Prop) : (term706 A _96501) = (term707 A _96501).
Proof. exact (MK_COMB (@lem7203435) (@lem7203434 A _96501)). Qed.
Lemma lem7203438 (a : Prop) : (term219 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7203439 {A : Type'} (R : type1626) (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term733 A R x _96499 _96500 _96501) = (term571 A R x _96499 _96500 _96501).
Proof. exact (@lem7203438 (term571 A R x _96499 _96500 _96501)). Qed.
Lemma lem7203440 {A : Type'} (R : type1626) (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term732 A R x _96499 _96500 _96501) = (term734 A R x _96499 _96500 _96501).
Proof. exact (MK_COMB (@lem7203436 A _96501) (@lem7203439 A R x _96499 _96500 _96501)). Qed.
Lemma lem7203441 {A : Type'} (R : type1626) (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term731 A R x _96499 _96500 _96501) = (term734 A R x _96499 _96500 _96501).
Proof. exact (TRANS (@lem7203431 A R x _96499 _96500 _96501) (@lem7203440 A R x _96499 _96500 _96501)). Qed.
Lemma lem7203442 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7203443 {A : Type'} (R : type1626) (x : type711 A) (_96499 : A -> real) (_96500 : A -> real) (_96501 : A -> Prop) : (term735 A R x _96499 _96500 _96501) = (term736 A R x _96499 _96500 _96501).
Proof. exact (MK_COMB (@lem7203442) (@lem7203441 A R x _96499 _96500 _96501)). Qed.
Lemma lem7203444 {A : Type'} (R : type1626) (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) : (term554 A R _96499 _96501 _96500) = (term554 A R _96499 _96501 _96500).
Proof. exact (eq_refl (term554 A R _96499 _96501 _96500)). Qed.
Lemma lem7203445 {A : Type'} (x : type711 A) (R : type1626) (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) : (term730 A x R _96499 _96501 _96500) = (term737 A x R _96499 _96501 _96500).
Proof. exact (MK_COMB (@lem7203443 A R x _96499 _96500 _96501) (@lem7203444 A R _96499 _96501 _96500)). Qed.
Lemma lem7203446 {A : Type'} (x : type711 A) (R : type1626) (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) : (term727 A R x _96499 _96500 _96501) = (term737 A x R _96499 _96501 _96500).
Proof. exact (TRANS (@lem7203428 A x R _96499 _96501 _96500) (@lem7203445 A x R _96499 _96501 _96500)). Qed.
Lemma lem7203448 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term601 A x R) (h3 : @FINITE A s) (h4 : term555 A R f s g) : term734 A R x f g s.
Proof. exact (conj (@lem7203169 A s h3) (@lem7203353 A x R f s g h1 h2 h3 h4)). Qed.
Lemma lem7203450 {A : Type'} (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) (x : type711 A) (R : type1626) (h1 : term601 A x R) : term737 A x R _96499 _96501 _96500.
Proof. exact (EQ_MP (@lem7203446 A x R _96499 _96501 _96500) (@lem7203425 A _96499 _96500 _96501 x R h1)). Qed.
Lemma lem7203451 {A : Type'} (_96499 : A -> real) (_96501 : A -> Prop) (_96500 : A -> real) (x : type711 A) (R : type1626) (h1 : term601 A x R) : term737 A x R _96499 _96501 _96500.
Proof. exact (@lem7203450 A _96499 _96501 _96500 x R h1). Qed.
Lemma lem7203452 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (x : type711 A) (R : type1626) (h1 : term601 A x R) : term737 A x R f s g.
Proof. exact (@lem7203451 A f s g x R h1). Qed.
Lemma lem7203455 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term601 A x R) (h3 : @FINITE A s) (h4 : term555 A R f s g) : term554 A R f s g.
Proof. exact (@lem7203452 A f s g x R h2 (@lem7203448 A x R f s g h1 h2 h3 h4)). Qed.
Lemma lem7203456 {A : Type'} (f : A -> real) (g : A -> real) (x : type711 A) (R : type1626) (s : A -> Prop) (h1 : term80 A s R f g) (h2 : term601 A x R) (h3 : @FINITE A s) : term738 A R f s g.
Proof. exact (fun h0 : term555 A R f s g => @lem7203455 A x R f s g h1 h2 h3 h0). Qed.
Lemma lem7203458 (p : Prop) : (term671 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7203459 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term738 A R f s g) = (term554 A R f s g).
Proof. exact (@lem7203458 (term554 A R f s g)). Qed.
Lemma lem7203460 {A : Type'} (f : A -> real) (g : A -> real) (x : type711 A) (R : type1626) (s : A -> Prop) (h1 : term80 A s R f g) (h2 : term601 A x R) (h3 : @FINITE A s) : term554 A R f s g.
Proof. exact (EQ_MP (@lem7203459 A R f s g) (@lem7203456 A f g x R s h1 h2 h3)). Qed.
Lemma lem7203463 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7203465 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term555 A R f s g) = (term739 A R f s g).
Proof. exact (@lem7203463 (term554 A R f s g)). Qed.
Lemma lem7203468 {A : Type'} (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term239 A R f s g) : term739 A R f s g.
Proof. exact (EQ_MP (@lem7203465 A R f s g) (@lem7203002 A R f s g h1)). Qed.
Lemma lem7203471 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term601 A x R) (h3 : @FINITE A s) (h4 : term239 A R f s g) : False.
Proof. exact (@lem7203468 A R f s g h4 (@lem7203460 A f g x R s h1 h2 h3)). Qed.
Lemma lem7203472 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term601 A x R) (h3 : @FINITE A s) (h4 : term239 A R f s g) : term691.
Proof. exact (fun h0 : ~ False => @lem7203471 A x R f s g h1 h2 h3 h4). Qed.
Lemma lem7203474 (p : Prop) : (term671 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7203475 : term691 = False.
Proof. exact (@lem7203474 False). Qed.
Lemma lem7203476 {A : Type'} (x : type711 A) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term601 A x R) (h3 : @FINITE A s) (h4 : term239 A R f s g) : False.
Proof. exact (EQ_MP (@lem7203475) (@lem7203472 A x R f s g h1 h2 h3 h4)). Qed.
Lemma lem7203477 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (x1 : real) (y1 : real) (x2 : real) (y2 : real) (x : type711 A) (R : type1626) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : @FINITE A s) (h4 : term239 A R f s g) (h5 : term499 A x1 y1 x2 y2 x R) : False.
Proof. exact (or_elim (@lem7202648 A x1 y1 x2 y2 x R h5) (fun h0 : term609 R x1 y1 x2 y2 => @lem7203162 R x1 y1 x2 y2 h2 h0) (fun h0 : term601 A x R => @lem7203476 A x R f s g h1 h0 h3 h4)). Qed.
Lemma lem7203478 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (y2 : real) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : term502 A x1 y1 x2 y2 R) (h4 : @FINITE A s) (h5 : term239 A R f s g) : False.
Proof. exact (ex_elim (@lem7202081 A x1 y1 x2 y2 R h3) (fun x : type711 A => fun h0 : term501 A x1 y1 x2 y2 R x => @lem7203477 A f s g x1 y1 x2 y2 x R h1 h2 h4 h5 h0)). Qed.
Lemma lem7203479 {A : Type'} (x1 : real) (y1 : real) (x2 : real) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : term504 A x1 y1 x2 R) (h4 : @FINITE A s) (h5 : term239 A R f s g) : False.
Proof. exact (ex_elim (@lem7202080 A x1 y1 x2 R h3) (fun y2 : real => fun h0 : term503 A x1 y1 x2 R y2 => @lem7203478 A x1 y1 x2 y2 R f s g h1 h2 h0 h4 h5)). Qed.
Lemma lem7203480 {A : Type'} (x1 : real) (y1 : real) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : term506 A x1 y1 R) (h4 : @FINITE A s) (h5 : term239 A R f s g) : False.
Proof. exact (ex_elim (@lem7202079 A x1 y1 R h3) (fun x2 : real => fun h0 : term505 A x1 y1 R x2 => @lem7203479 A x1 y1 x2 R f s g h1 h2 h0 h4 h5)). Qed.
Lemma lem7203481 {A : Type'} (x1 : real) (R : type1626) (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : term508 A x1 R) (h4 : @FINITE A s) (h5 : term239 A R f s g) : False.
Proof. exact (ex_elim (@lem7202078 A x1 R h3) (fun y1 : real => fun h0 : term507 A x1 R y1 => @lem7203480 A x1 y1 R f s g h1 h2 h0 h4 h5)). Qed.
Lemma lem7203482 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (R : type1626) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : @FINITE A s) (h4 : term239 A R f s g) (h5 : term206 A R) : False.
Proof. exact (ex_elim (@lem7202002 A R h5) (fun x1 : real => fun h0 : term509 A R x1 => @lem7203481 A x1 R f s g h1 h2 h0 h3 h4)). Qed.
Lemma lem7203483 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (R : type1626) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : @FINITE A s) (h4 : term239 A R f s g) (h5 : term206 A R) : (term239 A R f s g) = False.
Proof. exact (prop_ext (fun h6 : term239 A R f s g => @lem7203482 A f s g R h1 h2 h3 h4 h5) (fun h6 : False => @lem7202077 A R f s g h4)). Qed.
Lemma lem7203484 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (R : type1626) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : @FINITE A s) (h4 : term239 A R f s g) (h5 : term206 A R) : False.
Proof. exact (EQ_MP (@lem7203483 A f s g R h1 h2 h3 h4 h5) (@lem7202077 A R f s g h4)). Qed.
Lemma lem7203485 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (R : type1626) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : @FINITE A s) (h4 : term239 A R f s g) (h5 : term206 A R) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h6 : @FINITE A s => @lem7203484 A f s g R h1 h2 h3 h4 h5) (fun h6 : False => @lem7202008 A s h3)). Qed.
Lemma lem7203486 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (R : type1626) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : @FINITE A s) (h4 : term239 A R f s g) (h5 : term206 A R) : False.
Proof. exact (EQ_MP (@lem7203485 A f s g R h1 h2 h3 h4 h5) (@lem7202008 A s h3)). Qed.
Lemma lem7203487 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (R : type1626) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : @FINITE A s) (h4 : term239 A R f s g) (h5 : term206 A R) : (term239 A R f s g) = False.
Proof. exact (prop_ext (fun h6 : term239 A R f s g => @lem7203486 A f s g R h1 h2 h3 h4 h5) (fun h6 : False => @lem7201306 A R f s g h4)). Qed.
Lemma lem7203488 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (R : type1626) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : @FINITE A s) (h4 : term239 A R f s g) (h5 : term206 A R) : False.
Proof. exact (EQ_MP (@lem7203487 A f s g R h1 h2 h3 h4 h5) (@lem7201306 A R f s g h4)). Qed.
Lemma lem7203489 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (R : type1626) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : @FINITE A s) (h4 : term206 A R) : term238 A R f s g.
Proof. exact (fun h0 : term239 A R f s g => @lem7203488 A f s g R h1 h2 h3 h0 h4). Qed.
Lemma lem7203490 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (R : type1626) (h1 : term80 A s R f g) (h2 : term75 R) (h3 : @FINITE A s) (h4 : term206 A R) : term25 A R f s g.
Proof. exact (EQ_MP (@lem7201305 A R f s g) (@lem7203489 A f g s R h1 h2 h3 h4)). Qed.
Lemma lem7203491 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (R : type1626) (h1 : term75 R) (h2 : @FINITE A s) (h3 : term206 A R) : term230 A R f s g.
Proof. exact (fun h0 : term80 A s R f g => @lem7203490 A f g s R h0 h1 h2 h3). Qed.
Lemma lem7203492 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (R : type1626) (h1 : term75 R) (h2 : term206 A R) : term79 A R f s g.
Proof. exact (fun h0 : @FINITE A s => @lem7203491 A f g s R h1 h0 h2). Qed.
Lemma lem7203497 {A : Type'} (f : A -> real) (g : A -> real) (R : type1626) (h1 : term75 R) (h2 : term206 A R) : term112 A R f g.
Proof. exact (fun s : A -> Prop => @lem7203492 A f s g R h1 h2). Qed.
Lemma lem7203502 {A : Type'} (f : A -> real) (R : type1626) (h1 : term75 R) (h2 : term206 A R) : term143 A R f.
Proof. exact (fun g : A -> real => @lem7203497 A f g R h1 h2). Qed.
Lemma lem7203507 {A : Type'} (R : type1626) (h1 : term75 R) (h2 : term206 A R) : term172 A R.
Proof. exact (fun f : A -> real => @lem7203502 A f R h1 h2). Qed.
Lemma lem7203508 {A : Type'} (R : type1626) (h1 : term75 R) : term210 A R.
Proof. exact (fun h0 : term206 A R => @lem7203507 A R h1 h0). Qed.
Lemma lem7203509 {A : Type'} (R : type1626) : term221 A R.
Proof. exact (fun h0 : term75 R => @lem7203508 A R h0). Qed.
Lemma lem7203510 {A : Type'} (R : type1626) : term222 A R.
Proof. exact (fun h0 : term23 R => @lem7203509 A R). Qed.
Lemma lem7203515 {A : Type'} : term226 A.
Proof. exact (fun R : type1626 => @lem7203510 A R). Qed.
Lemma lem7203516 {A : Type'} : term225 A.
Proof. exact (EQ_MP (@lem7201296 A) (@lem7203515 A)). Qed.
Lemma lem7203517 {A : Type'} (R : type1626) : term740 A R.
Proof. exact (@lem7203516 A R). Qed.
Lemma lem7203518 {A : Type'} (R : type1626) : (term740 A R) = (term214 A R).
Proof. exact (eq_refl (term740 A R)). Qed.
Lemma lem7203519 {A : Type'} (R : type1626) : term214 A R.
Proof. exact (EQ_MP (@lem7203518 A R) (@lem7203517 A R)). Qed.
Lemma lem7203521 {A : Type'} (R : type1626) : term214 A R.
Proof. exact (@lem7200932 A R (@lem7203519 A R)). Qed.
Lemma lem7203522 {A : Type'} (R : type1626) (h1 : term23 R) : term220 A R.
Proof. exact (@lem7203521 A R (@lem7200738 R h1)). Qed.
Lemma lem7203523 {A : Type'} (R : type1626) (h1 : term75 R) (h2 : term23 R) : term212 A R.
Proof. exact (@lem7203522 A R h2 (@lem7200739 R h1)). Qed.
Lemma lem7203524 {A : Type'} (R : type1626) (h1 : term75 R) (h2 : term213 A R) (h3 : term23 R) : False.
Proof. exact (@lem7203523 A R h1 h3 (@lem7200916 A R h2)). Qed.
Lemma lem7203525 {A : Type'} (R : type1626) (h1 : term75 R) (h2 : term213 A R) (h3 : term23 R) : (term213 A R) = False.
Proof. exact (prop_ext (fun h4 : term213 A R => @lem7203524 A R h1 h2 h3) (fun h4 : False => @lem7200916 A R h2)). Qed.
Lemma lem7203526 {A : Type'} (R : type1626) (h1 : term75 R) (h2 : term213 A R) (h3 : term23 R) : False.
Proof. exact (EQ_MP (@lem7203525 A R h1 h2 h3) (@lem7200916 A R h2)). Qed.
Lemma lem7203527 {A : Type'} (R : type1626) (h1 : term75 R) (h2 : term23 R) : term212 A R.
Proof. exact (fun h0 : term213 A R => @lem7203526 A R h1 h0 h2). Qed.
Lemma lem7203528 {A : Type'} (R : type1626) (h1 : term75 R) (h2 : term23 R) : term210 A R.
Proof. exact (EQ_MP (@lem7200915 A R) (@lem7203527 A R h1 h2)). Qed.
Lemma lem7203529 {A : Type'} (R : type1626) (h1 : term75 R) (h2 : term23 R) : term209 A R.
Proof. exact (EQ_MP (@lem7200911 A R h2) (@lem7203528 A R h1 h2)). Qed.
Lemma lem7203530 {A : Type'} (R : type1626) (h1 : term75 R) (h2 : term23 R) : term172 A R.
Proof. exact (@lem7203529 A R h1 h2 (@lem7199915 A R)). Qed.
Lemma lem7203531 {A : Type'} (R : type1626) (h1 : term23 R) : term173 A R.
Proof. exact (fun h0 : term75 R => @lem7203530 A R h0 h1). Qed.
Lemma lem7203532 {A : Type'} (R : type1626) : term174 A R.
Proof. exact (fun h0 : term23 R => @lem7203531 A R h0). Qed.
Lemma lem7203537 {A : Type'} : term178 A.
Proof. exact (fun R : type1626 => @lem7203532 A R). Qed.
Lemma lem7203538 {A : Type'} : term177 A.
Proof. exact (EQ_MP (@lem7200737 A) (@lem7203537 A)). Qed.
