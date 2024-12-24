Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1254205_term_abbrevs.
Require Import EQ_ADD_LCANCEL_spec.
Require Import thm0_spec.
Require Import thm272789_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1253870 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1253871 (x : nat) : (x = x) = True.
Proof. exact (@lem1253870 nat x). Qed.
Lemma lem1253872 (p : nat) (n : nat) (d'' : nat) : ((term0 p n d'') = (term0 p n d'')) = True.
Proof. exact (@lem1253871 (term0 p n d'')). Qed.
Lemma lem1253873 (p : nat) (n : nat) (d'' : nat) : True = ((term0 p n d'') = (term0 p n d'')).
Proof. exact (SYM (@lem1253872 p n d'')). Qed.
Lemma lem1253874 (p : nat) (n : nat) (d'' : nat) : (term0 p n d'') = (term0 p n d'').
Proof. exact (EQ_MP (@lem1253873 p n d'') (@lem0)). Qed.
Lemma lem1253878 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1253879 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term2 p n d' d'' d''') = (term3 p n d' d'' d''').
Proof. exact (@lem1253878 (Nat.add p d') n (term4 d' d'' d''')). Qed.
Lemma lem1253881 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1253882 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term3 p n d' d'' d''') = (term5 p n d' d'' d''').
Proof. exact (@lem1253881 p d' (term6 n d' d'' d''')). Qed.
Lemma lem1253884 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253885 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term5 p n d' d'' d''') = (term7 p n d' d'' d''').
Proof. exact (@lem1253884 d' p (term6 n d' d'' d''')). Qed.
Lemma lem1253892 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term3 p n d' d'' d''') = (term7 p n d' d'' d''').
Proof. exact (TRANS (@lem1253882 p n d' d'' d''') (@lem1253885 p n d' d'' d''')). Qed.
Lemma lem1253893 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term2 p n d' d'' d''') = (term7 p n d' d'' d''').
Proof. exact (TRANS (@lem1253879 p n d' d'' d''') (@lem1253892 p n d' d'' d''')). Qed.
Lemma lem1253895 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253896 (n : nat) (p : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term8 p n d' d'' d''') = (term8 n p d' d'' d''').
Proof. exact (@lem1253895 n p (term4 d' d'' d''')). Qed.
Lemma lem1253910 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1253911 (d' : nat) (d'' : nat) (d''' : nat) : (term4 d' d'' d''') = (term9 d' d'' d''').
Proof. exact (@lem1253910 d' d'' (S d''')). Qed.
Lemma lem1253921 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem1253922 (p : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term6 p d' d'' d''') = (term10 p d' d'' d''').
Proof. exact (MK_COMB (@lem1253921 p) (@lem1253911 d' d'' d''')). Qed.
Lemma lem1253924 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253925 (d' : nat) (p : nat) (d'' : nat) (d''' : nat) : (term10 p d' d'' d''') = (term10 d' p d'' d''').
Proof. exact (@lem1253924 d' p (term11 d'' d''')). Qed.
Lemma lem1253933 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253934 (d'' : nat) (p : nat) (d''' : nat) : (term9 p d'' d''') = (term9 d'' p d''').
Proof. exact (@lem1253933 d'' p (S d''')). Qed.
Lemma lem1253944 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1253945 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term10 d' p d'' d''') = (term10 d' d'' p d''').
Proof. exact (MK_COMB (@lem1253944 d') (@lem1253934 d'' p d''')). Qed.
Lemma lem1253952 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term10 p d' d'' d''') = (term10 d' d'' p d''').
Proof. exact (TRANS (@lem1253925 d' p d'' d''') (@lem1253945 d' d'' p d''')). Qed.
Lemma lem1253953 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term6 p d' d'' d''') = (term10 d' d'' p d''').
Proof. exact (TRANS (@lem1253922 p d' d'' d''') (@lem1253952 d' d'' p d''')). Qed.
Lemma lem1253954 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem1253955 (n : nat) (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term8 n p d' d'' d''') = (term12 n d' d'' p d''').
Proof. exact (MK_COMB (@lem1253954 n) (@lem1253953 d' d'' p d''')). Qed.
Lemma lem1253957 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253958 (d' : nat) (n : nat) (d'' : nat) (p : nat) (d''' : nat) : (term12 n d' d'' p d''') = (term12 d' n d'' p d''').
Proof. exact (@lem1253957 d' n (term9 d'' p d''')). Qed.
Lemma lem1253966 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253967 (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term10 n d'' p d''') = (term10 d'' n p d''').
Proof. exact (@lem1253966 d'' n (term11 p d''')). Qed.
Lemma lem1253983 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1253984 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term12 d' n d'' p d''') = (term12 d' d'' n p d''').
Proof. exact (MK_COMB (@lem1253983 d') (@lem1253967 d'' n p d''')). Qed.
Lemma lem1253991 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term12 n d' d'' p d''') = (term12 d' d'' n p d''').
Proof. exact (TRANS (@lem1253958 d' n d'' p d''') (@lem1253984 d' d'' n p d''')). Qed.
Lemma lem1253992 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term8 n p d' d'' d''') = (term12 d' d'' n p d''').
Proof. exact (TRANS (@lem1253955 n d' d'' p d''') (@lem1253991 d' d'' n p d''')). Qed.
Lemma lem1253993 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term8 p n d' d'' d''') = (term12 d' d'' n p d''').
Proof. exact (TRANS (@lem1253896 n p d' d'' d''') (@lem1253992 d' d'' n p d''')). Qed.
Lemma lem1253994 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1253995 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term7 p n d' d'' d''') = (term13 d' d'' n p d''').
Proof. exact (MK_COMB (@lem1253994 d') (@lem1253993 d' d'' n p d''')). Qed.
Lemma lem1254002 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term2 p n d' d'' d''') = (term13 d' d'' n p d''').
Proof. exact (TRANS (@lem1253893 p n d' d'' d''') (@lem1253995 d' d'' n p d''')). Qed.
Lemma lem1254003 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1254004 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term14 p n d' d'' d''') = (term15 d' d'' n p d''').
Proof. exact (MK_COMB (@lem1254003) (@lem1254002 d' d'' n p d''')). Qed.
Lemma lem1254006 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254007 (n : nat) (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term16 p n d'' d' d''') = (term16 n p d'' d' d''').
Proof. exact (@lem1254006 n p (term17 d'' d' d''')). Qed.
Lemma lem1254015 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254016 (d'' : nat) (p : nat) (d' : nat) (d''' : nat) : (term18 p d'' d' d''') = (term18 d'' p d' d''').
Proof. exact (@lem1254015 d'' p (term19 d' d''')). Qed.
Lemma lem1254024 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254025 (p : nat) (d' : nat) (d''' : nat) : (term17 p d' d''') = (term20 p d' d''').
Proof. exact (@lem1254024 d' p (term11 d' d''')). Qed.
Lemma lem1254033 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254034 (d' : nat) (p : nat) (d''' : nat) : (term9 p d' d''') = (term9 d' p d''').
Proof. exact (@lem1254033 d' p (S d''')). Qed.
Lemma lem1254044 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1254045 (d' : nat) (p : nat) (d''' : nat) : (term20 p d' d''') = (term21 d' p d''').
Proof. exact (MK_COMB (@lem1254044 d') (@lem1254034 d' p d''')). Qed.
Lemma lem1254052 (d' : nat) (p : nat) (d''' : nat) : (term17 p d' d''') = (term21 d' p d''').
Proof. exact (TRANS (@lem1254025 p d' d''') (@lem1254045 d' p d''')). Qed.
Lemma lem1254053 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1254054 (d'' : nat) (d' : nat) (p : nat) (d''' : nat) : (term18 d'' p d' d''') = (term22 d'' d' p d''').
Proof. exact (MK_COMB (@lem1254053 d'') (@lem1254052 d' p d''')). Qed.
Lemma lem1254056 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254057 (d'' : nat) (d' : nat) (p : nat) (d''' : nat) : (term22 d'' d' p d''') = (term23 d'' d' p d''').
Proof. exact (@lem1254056 d' d'' (term9 d' p d''')). Qed.
Lemma lem1254065 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254066 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term10 d'' d' p d''') = (term10 d' d'' p d''').
Proof. exact (@lem1254065 d' d'' (term11 p d''')). Qed.
Lemma lem1254082 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1254083 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term23 d'' d' p d''') = (term24 d' d'' p d''').
Proof. exact (MK_COMB (@lem1254082 d') (@lem1254066 d' d'' p d''')). Qed.
Lemma lem1254090 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term22 d'' d' p d''') = (term24 d' d'' p d''').
Proof. exact (TRANS (@lem1254057 d'' d' p d''') (@lem1254083 d' d'' p d''')). Qed.
Lemma lem1254091 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term18 d'' p d' d''') = (term24 d' d'' p d''').
Proof. exact (TRANS (@lem1254054 d'' d' p d''') (@lem1254090 d' d'' p d''')). Qed.
Lemma lem1254092 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term18 p d'' d' d''') = (term24 d' d'' p d''').
Proof. exact (TRANS (@lem1254016 d'' p d' d''') (@lem1254091 d' d'' p d''')). Qed.
Lemma lem1254093 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem1254094 (n : nat) (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term16 n p d'' d' d''') = (term25 n d' d'' p d''').
Proof. exact (MK_COMB (@lem1254093 n) (@lem1254092 d' d'' p d''')). Qed.
Lemma lem1254096 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254097 (n : nat) (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term25 n d' d'' p d''') = (term26 n d' d'' p d''').
Proof. exact (@lem1254096 d' n (term10 d' d'' p d''')). Qed.
Lemma lem1254105 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254106 (d' : nat) (n : nat) (d'' : nat) (p : nat) (d''' : nat) : (term12 n d' d'' p d''') = (term12 d' n d'' p d''').
Proof. exact (@lem1254105 d' n (term9 d'' p d''')). Qed.
Lemma lem1254114 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254115 (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term10 n d'' p d''') = (term10 d'' n p d''').
Proof. exact (@lem1254114 d'' n (term11 p d''')). Qed.
Lemma lem1254131 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1254132 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term12 d' n d'' p d''') = (term12 d' d'' n p d''').
Proof. exact (MK_COMB (@lem1254131 d') (@lem1254115 d'' n p d''')). Qed.
Lemma lem1254139 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term12 n d' d'' p d''') = (term12 d' d'' n p d''').
Proof. exact (TRANS (@lem1254106 d' n d'' p d''') (@lem1254132 d' d'' n p d''')). Qed.
Lemma lem1254140 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1254141 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term26 n d' d'' p d''') = (term13 d' d'' n p d''').
Proof. exact (MK_COMB (@lem1254140 d') (@lem1254139 d' d'' n p d''')). Qed.
Lemma lem1254148 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term25 n d' d'' p d''') = (term13 d' d'' n p d''').
Proof. exact (TRANS (@lem1254097 n d' d'' p d''') (@lem1254141 d' d'' n p d''')). Qed.
Lemma lem1254149 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term16 n p d'' d' d''') = (term13 d' d'' n p d''').
Proof. exact (TRANS (@lem1254094 n d' d'' p d''') (@lem1254148 d' d'' n p d''')). Qed.
Lemma lem1254150 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term16 p n d'' d' d''') = (term13 d' d'' n p d''').
Proof. exact (TRANS (@lem1254007 n p d'' d' d''') (@lem1254149 d' d'' n p d''')). Qed.
Lemma lem1254151 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : ((term2 p n d' d'' d''') = (term16 p n d'' d' d''')) = ((term13 d' d'' n p d''') = (term13 d' d'' n p d''')).
Proof. exact (MK_COMB (@lem1254004 d' d'' n p d''') (@lem1254150 d' d'' n p d''')). Qed.
Lemma lem1254153 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1254154 (x : nat) : (x = x) = True.
Proof. exact (@lem1254153 nat x). Qed.
Lemma lem1254155 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : ((term13 d' d'' n p d''') = (term13 d' d'' n p d''')) = True.
Proof. exact (@lem1254154 (term13 d' d'' n p d''')). Qed.
Lemma lem1254156 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term2 p n d' d'' d''') = (term16 p n d'' d' d''')) = True.
Proof. exact (TRANS (@lem1254151 d' d'' n p d''') (@lem1254155 d' d'' n p d''')). Qed.
Lemma lem1254157 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : True = ((term2 p n d' d'' d''') = (term16 p n d'' d' d''')).
Proof. exact (SYM (@lem1254156 p n d'' d' d''')). Qed.
Lemma lem1254158 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term2 p n d' d'' d''') = (term16 p n d'' d' d''').
Proof. exact (EQ_MP (@lem1254157 p n d'' d' d''') (@lem0)). Qed.
Lemma lem1254159 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1254160 (p : nat) (n : nat) (d'' : nat) : (term27 p n d'') = (term27 p n d'').
Proof. exact (MK_COMB (@lem1254159) (@lem1253874 p n d'')). Qed.
Lemma lem1254161 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term0 p n d'') = (term2 p n d' d'' d''')) = ((term0 p n d'') = (term16 p n d'' d' d''')).
Proof. exact (MK_COMB (@lem1254160 p n d'') (@lem1254158 p n d'' d' d''')). Qed.
Lemma lem1254162 (m : nat) : term28 m.
Proof. exact (@lem272789 m). Qed.
Lemma lem1254163 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem1254164 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem1254163 m) (@lem1254162 m)). Qed.
Lemma lem1254165 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem1254164 m n). Qed.
Lemma lem1254166 (m : nat) (n : nat) : (term30 m n) = ((m = (Nat.add m n)) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem1254174 (m : nat) : term31 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1254175 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem1254176 (m : nat) : term32 m.
Proof. exact (EQ_MP (@lem1254175 m) (@lem1254174 m)). Qed.
Lemma lem1254177 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem1254176 m n). Qed.
Lemma lem1254178 (m : nat) (n : nat) : (term33 m n) = (term34 m n).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem1254179 (m : nat) (n : nat) : term34 m n.
Proof. exact (EQ_MP (@lem1254178 m n) (@lem1254177 m n)). Qed.
Lemma lem1254180 (m : nat) (n : nat) (p : nat) : term35 m n p.
Proof. exact (@lem1254179 m n p). Qed.
Lemma lem1254181 (m : nat) (n : nat) (p : nat) : (term35 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term35 m n p)). Qed.
Lemma lem1254184 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1254181 m n p) (@lem1254180 m n p)). Qed.
Lemma lem1254185 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term0 p n d'') = (term16 p n d'' d' d''')) = ((Nat.add n d'') = (term18 n d'' d' d''')).
Proof. exact (@lem1254184 p (Nat.add n d'') (term18 n d'' d' d''')). Qed.
Lemma lem1254187 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1254181 m n p) (@lem1254180 m n p)). Qed.
Lemma lem1254188 (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add n d'') = (term18 n d'' d' d''')) = (d'' = (term17 d'' d' d''')).
Proof. exact (@lem1254187 n d'' (term17 d'' d' d''')). Qed.
Lemma lem1254190 (m : nat) (n : nat) : (m = (Nat.add m n)) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1254166 m n) (@lem1254165 m n)). Qed.
Lemma lem1254195 (d'' : nat) (d' : nat) (d''' : nat) : (d'' = (term17 d'' d' d''')) = ((term19 d' d''') = (NUMERAL 0)).
Proof. exact (@lem1254190 d'' (term19 d' d''')). Qed.
Lemma lem1254196 (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add n d'') = (term18 n d'' d' d''')) = ((term19 d' d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1254188 n d'' d' d''') (@lem1254195 d'' d' d''')). Qed.
Lemma lem1254197 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term0 p n d'') = (term16 p n d'' d' d''')) = ((term19 d' d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1254185 p n d'' d' d''') (@lem1254196 n d'' d' d''')). Qed.
Lemma lem1254198 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term36 p n d' d'' d''') = (term36 p n d' d'' d''').
Proof. exact (eq_refl (term36 p n d' d'' d''')). Qed.
Lemma lem1254199 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (((term0 p n d'') = (term2 p n d' d'' d''')) = ((term0 p n d'') = (term16 p n d'' d' d'''))) = (((term0 p n d'') = (term2 p n d' d'' d''')) = ((term19 d' d''') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1254198 p n d' d'' d''') (@lem1254197 p n d'' d' d''')). Qed.
Lemma lem1254200 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term0 p n d'') = (term2 p n d' d'' d''')) = ((term19 d' d''') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1254199 p n d'' d' d''') (@lem1254161 p n d'' d' d''')). Qed.
Lemma lem1254201 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1254202 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term37 p n d' d'' d''') = (term38 d' d''').
Proof. exact (MK_COMB (@lem1254201) (@lem1254200 p n d'' d' d''')). Qed.
Lemma lem1254203 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1254204 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term39 p n d' d'' d''') = (term40 d' d''').
Proof. exact (MK_COMB (@lem1254202 p n d'' d' d''') (@lem1254203)). Qed.
Lemma lem1254205 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term40 d' d''') = (term39 p n d' d'' d''').
Proof. exact (SYM (@lem1254204 p n d'' d' d''')). Qed.
