Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_BOUND_term_abbrevs.
Require Import ADD_AC_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import MULT_AC_spec.
Require Import MULT_CLAUSES_spec.
Require Import NADD_CAUCHY_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import thm0_spec.
Require Import thm1247096_spec.
Require Import thm1823_spec.
Lemma lem1262856 (n : nat) (m : nat) (p : nat) : term0 n m p.
Proof. exact (proj2 (@lem79120 n m p)). Qed.
Lemma lem1262860 : term1.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1262861 : term2.
Proof. exact (proj2 (@lem1262860)). Qed.
Lemma lem1262862 : term3.
Proof. exact (proj2 (@lem1262861)). Qed.
Lemma lem1262878 : term4.
Proof. exact (proj1 (@lem1262862)). Qed.
Lemma lem1262879 (m : nat) : term5 m.
Proof. exact (@lem1262878 m). Qed.
Lemma lem1262880 (m : nat) : (term5 m) = ((term6 m) = m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem1262894 (m : nat) : term7 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1262895 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem1262896 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem1262895 m) (@lem1262894 m)). Qed.
Lemma lem1262897 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem1262896 m n). Qed.
Lemma lem1262898 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem1262899 (m : nat) (n : nat) : term10 m n.
Proof. exact (EQ_MP (@lem1262898 m n) (@lem1262897 m n)). Qed.
Lemma lem1262900 (m : nat) (n : nat) (p : nat) : term11 m n p.
Proof. exact (@lem1262899 m n p). Qed.
Lemma lem1262901 (m : nat) (n : nat) (p : nat) : (term11 m n p) = ((term12 m n p) = (term13 m n p)).
Proof. exact (eq_refl (term11 m n p)). Qed.
Lemma lem1262903 (m : nat) : term14 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem1262904 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem1262905 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem1262904 m) (@lem1262903 m)). Qed.
Lemma lem1262906 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem1262905 m n). Qed.
Lemma lem1262907 (n : nat) (m : nat) : (term16 m n) = (term17 n m).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem1262908 (n : nat) (m : nat) : term17 n m.
Proof. exact (EQ_MP (@lem1262907 n m) (@lem1262906 m n)). Qed.
Lemma lem1262909 (n : nat) (m : nat) (p : nat) : term18 n m p.
Proof. exact (@lem1262908 n m p). Qed.
Lemma lem1262910 (n : nat) (m : nat) (p : nat) : (term18 n m p) = ((term19 m n p) = (term20 n m p)).
Proof. exact (eq_refl (term18 n m p)). Qed.
Lemma lem1262912 : term1.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1262913 : term2.
Proof. exact (proj2 (@lem1262912)). Qed.
Lemma lem1262934 : term21.
Proof. exact (proj1 (@lem1262913)). Qed.
Lemma lem1262935 (n : nat) : term22 n.
Proof. exact (@lem1262934 n). Qed.
Lemma lem1262936 (n : nat) : (term22 n) = ((term23 n) = n).
Proof. exact (eq_refl (term22 n)). Qed.
Lemma lem1262946 (m : nat) : term24 m.
Proof. exact (@lem1247096 m). Qed.
Lemma lem1262947 (m : nat) : (term24 m) = (term25 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem1262948 (m : nat) : term25 m.
Proof. exact (EQ_MP (@lem1262947 m) (@lem1262946 m)). Qed.
Lemma lem1262949 (m : nat) (n : nat) : term26 m n.
Proof. exact (@lem1262948 m n). Qed.
Lemma lem1262950 (n : nat) (m : nat) : (term26 m n) = (term27 n m).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem1262951 (n : nat) (m : nat) : term27 n m.
Proof. exact (EQ_MP (@lem1262950 n m) (@lem1262949 m n)). Qed.
Lemma lem1262952 (n : nat) (m : nat) (p : nat) : term28 n m p.
Proof. exact (@lem1262951 n m p). Qed.
Lemma lem1262953 (n : nat) (m : nat) (p : nat) : (term28 n m p) = ((term29 m n p) = (term30 n m p)).
Proof. exact (eq_refl (term28 n m p)). Qed.
Lemma lem1262955 (x : nadd) : term31 x.
Proof. exact (@lem1262851 x). Qed.
Lemma lem1262956 (x : nadd) : (term31 x) = (term32 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1262957 (x : nadd) : term32 x.
Proof. exact (EQ_MP (@lem1262956 x) (@lem1262955 x)). Qed.
Lemma lem1262958 (x : nadd) (B : nat) (h1 : term33 x B) : term33 x B.
Proof. exact (h1). Qed.
Lemma lem1262959 (n : nat) (x : nadd) (B : nat) (h1 : term33 x B) : term34 x B n.
Proof. exact (@lem1262958 x B h1 n). Qed.
Lemma lem1262960 (x : nadd) (B : nat) (n : nat) : (term34 x B n) = (term35 x B n).
Proof. exact (eq_refl (term34 x B n)). Qed.
Lemma lem1262961 (n : nat) (x : nadd) (B : nat) (h1 : term33 x B) : term35 x B n.
Proof. exact (EQ_MP (@lem1262960 x B n) (@lem1262959 n x B h1)). Qed.
Lemma lem1262962 (n : nat) (x : nadd) (B : nat) (h1 : term33 x B) : term36 x B n.
Proof. exact (@lem1262961 n x B h1 term37). Qed.
Lemma lem1262963 (x : nadd) (B : nat) (n : nat) : (term36 x B n) = (term38 x B n).
Proof. exact (eq_refl (term36 x B n)). Qed.
Lemma lem1262964 (n : nat) (x : nadd) (B : nat) (h1 : term33 x B) : term38 x B n.
Proof. exact (EQ_MP (@lem1262963 x B n) (@lem1262962 n x B h1)). Qed.
Lemma lem1262968 (n : nat) (m : nat) (p : nat) : (term29 m n p) = (term30 n m p).
Proof. exact (EQ_MP (@lem1262953 n m p) (@lem1262952 n m p)). Qed.
Lemma lem1262969 (x : nadd) (B : nat) (n : nat) : (term38 x B n) = (term39 x B n).
Proof. exact (@lem1262968 (term40 x n) (term41 n x) (term42 B n)). Qed.
Lemma lem1262973 (n : nat) : (term23 n) = n.
Proof. exact (EQ_MP (@lem1262936 n) (@lem1262935 n)). Qed.
Lemma lem1262974 (x : nadd) (n : nat) : (term40 x n) = (dest_nadd x n).
Proof. exact (@lem1262973 (dest_nadd x n)). Qed.
Lemma lem1262975 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1262976 (x : nadd) (n : nat) : (term43 x n) = (term44 x n).
Proof. exact (MK_COMB (@lem1262975) (@lem1262974 x n)). Qed.
Lemma lem1262977 (B : nat) (n : nat) : (term42 B n) = (term42 B n).
Proof. exact (eq_refl (term42 B n)). Qed.
Lemma lem1262978 (x : nadd) (B : nat) (n : nat) : (term45 x B n) = (term46 x B n).
Proof. exact (MK_COMB (@lem1262976 x n) (@lem1262977 B n)). Qed.
Lemma lem1262979 (n : nat) (x : nadd) : (term47 n x) = (term47 n x).
Proof. exact (eq_refl (term47 n x)). Qed.
Lemma lem1262980 (x : nadd) (B : nat) (n : nat) : (term48 x B n) = (term49 x B n).
Proof. exact (MK_COMB (@lem1262979 n x) (@lem1262978 x B n)). Qed.
Lemma lem1262981 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1262982 (x : nadd) (B : nat) (n : nat) : (term50 x B n) = (term51 x B n).
Proof. exact (MK_COMB (@lem1262981) (@lem1262980 x B n)). Qed.
Lemma lem1262984 (n : nat) : (term23 n) = n.
Proof. exact (EQ_MP (@lem1262936 n) (@lem1262935 n)). Qed.
Lemma lem1262985 (x : nadd) (n : nat) : (term40 x n) = (dest_nadd x n).
Proof. exact (@lem1262984 (dest_nadd x n)). Qed.
Lemma lem1262986 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1262987 (x : nadd) (n : nat) : (term52 x n) = (term53 x n).
Proof. exact (MK_COMB (@lem1262986) (@lem1262985 x n)). Qed.
Lemma lem1262988 (x : nadd) (B : nat) (n : nat) : (term54 x B n) = (term54 x B n).
Proof. exact (eq_refl (term54 x B n)). Qed.
Lemma lem1262989 (x : nadd) (B : nat) (n : nat) : (term55 x B n) = (term56 x B n).
Proof. exact (MK_COMB (@lem1262987 x n) (@lem1262988 x B n)). Qed.
Lemma lem1262990 (x : nadd) (B : nat) (n : nat) : (term39 x B n) = (term57 x B n).
Proof. exact (MK_COMB (@lem1262982 x B n) (@lem1262989 x B n)). Qed.
Lemma lem1262993 (x : nadd) (B : nat) (n : nat) : (term38 x B n) = (term57 x B n).
Proof. exact (TRANS (@lem1262969 x B n) (@lem1262990 x B n)). Qed.
Lemma lem1262994 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1262995 (x : nadd) (B : nat) (n : nat) : (term58 x B n) = (term59 x B n).
Proof. exact (MK_COMB (@lem1262994) (@lem1262993 x B n)). Qed.
Lemma lem1262996 (x : nadd) (n : nat) (B : nat) : (term60 x n B) = (term60 x n B).
Proof. exact (eq_refl (term60 x n B)). Qed.
Lemma lem1262997 (x : nadd) (n : nat) (B : nat) : (term61 x n B) = (term62 x n B).
Proof. exact (MK_COMB (@lem1262995 x B n) (@lem1262996 x n B)). Qed.
Lemma lem1263000 (x : nadd) (n : nat) (B : nat) : (term62 x n B) = (term61 x n B).
Proof. exact (SYM (@lem1262997 x n B)). Qed.
Lemma lem1263001 (x : nadd) (B : nat) (n : nat) (h1 : term57 x B n) : term57 x B n.
Proof. exact (h1). Qed.
Lemma lem1263002 (x : nadd) (B : nat) (n : nat) (h1 : term57 x B n) : term56 x B n.
Proof. exact (proj2 (@lem1263001 x B n h1)). Qed.
Lemma lem1263006 (n : nat) (m : nat) (p : nat) : (term19 m n p) = (term20 n m p).
Proof. exact (EQ_MP (@lem1262910 n m p) (@lem1262909 n m p)). Qed.
Lemma lem1263007 (n : nat) (B : nat) : (term42 B n) = (term63 n B).
Proof. exact (@lem1263006 n B term37). Qed.
Lemma lem1263009 (m : nat) : (term6 m) = m.
Proof. exact (EQ_MP (@lem1262880 m) (@lem1262879 m)). Qed.
Lemma lem1263010 (B : nat) : (term6 B) = B.
Proof. exact (@lem1263009 B). Qed.
Lemma lem1263011 (B : nat) (n : nat) : (term64 B n) = (term64 B n).
Proof. exact (eq_refl (term64 B n)). Qed.
Lemma lem1263012 (n : nat) (B : nat) : (term63 n B) = (term65 n B).
Proof. exact (MK_COMB (@lem1263011 B n) (@lem1263010 B)). Qed.
Lemma lem1263013 (n : nat) (B : nat) : (term42 B n) = (term65 n B).
Proof. exact (TRANS (@lem1263007 n B) (@lem1263012 n B)). Qed.
Lemma lem1263014 (n : nat) (x : nadd) : (term66 n x) = (term66 n x).
Proof. exact (eq_refl (term66 n x)). Qed.
Lemma lem1263015 (x : nadd) (n : nat) (B : nat) : (term54 x B n) = (term67 x n B).
Proof. exact (MK_COMB (@lem1263014 n x) (@lem1263013 n B)). Qed.
Lemma lem1263016 (x : nadd) (n : nat) : (term53 x n) = (term53 x n).
Proof. exact (eq_refl (term53 x n)). Qed.
Lemma lem1263017 (x : nadd) (n : nat) (B : nat) : (term56 x B n) = (term68 x n B).
Proof. exact (MK_COMB (@lem1263016 x n) (@lem1263015 x n B)). Qed.
Lemma lem1263018 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1263019 (x : nadd) (n : nat) (B : nat) : (term69 x B n) = (term70 x n B).
Proof. exact (MK_COMB (@lem1263018) (@lem1263017 x n B)). Qed.
Lemma lem1263021 (m : nat) (n : nat) (p : nat) : (term12 m n p) = (term13 m n p).
Proof. exact (EQ_MP (@lem1262901 m n p) (@lem1262900 m n p)). Qed.
Lemma lem1263022 (B : nat) (x : nadd) (n : nat) : (term71 B x n) = (term72 B x n).
Proof. exact (@lem1263021 B (term73 x) n). Qed.
Lemma lem1263023 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1263024 (B : nat) (x : nadd) (n : nat) : (term74 B x n) = (term75 B x n).
Proof. exact (MK_COMB (@lem1263023) (@lem1263022 B x n)). Qed.
Lemma lem1263025 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1263026 (x : nadd) (n : nat) (B : nat) : (term76 x n B) = (term77 x n B).
Proof. exact (MK_COMB (@lem1263024 B x n) (@lem1263025 B)). Qed.
Lemma lem1263027 (x : nadd) (n : nat) : (term53 x n) = (term53 x n).
Proof. exact (eq_refl (term53 x n)). Qed.
Lemma lem1263028 (x : nadd) (n : nat) (B : nat) : (term60 x n B) = (term78 x n B).
Proof. exact (MK_COMB (@lem1263027 x n) (@lem1263026 x n B)). Qed.
Lemma lem1263029 (x : nadd) (n : nat) (B : nat) : (term79 x n B) = (term80 x n B).
Proof. exact (MK_COMB (@lem1263019 x n B) (@lem1263028 x n B)). Qed.
Lemma lem1263032 (x : nadd) (n : nat) (B : nat) : (term80 x n B) = (term79 x n B).
Proof. exact (SYM (@lem1263029 x n B)). Qed.
Lemma lem1263036 (n : nat) (m : nat) (p : nat) : (term81 m n p) = (term81 n m p).
Proof. exact (proj2 (@lem1262856 n m p)). Qed.
Lemma lem1263037 (n : nat) (x : nadd) (B : nat) : (term67 x n B) = (term82 n x B).
Proof. exact (@lem1263036 (Nat.mul B n) (term41 n x) B). Qed.
Lemma lem1263048 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1263049 (B : nat) (n : nat) (x : nadd) : (term83 n x B) = (term84 B n x).
Proof. exact (@lem1263048 B (term41 n x)). Qed.
Lemma lem1263056 (B : nat) (n : nat) : (term64 B n) = (term64 B n).
Proof. exact (eq_refl (term64 B n)). Qed.
Lemma lem1263057 (B : nat) (n : nat) (x : nadd) : (term82 n x B) = (term85 B n x).
Proof. exact (MK_COMB (@lem1263056 B n) (@lem1263049 B n x)). Qed.
Lemma lem1263059 (n : nat) (m : nat) (p : nat) : (term81 m n p) = (term81 n m p).
Proof. exact (proj2 (@lem1262856 n m p)). Qed.
Lemma lem1263060 (B : nat) (n : nat) (x : nadd) : (term85 B n x) = (term86 B n x).
Proof. exact (@lem1263059 B (Nat.mul B n) (term41 n x)). Qed.
Lemma lem1263076 (B : nat) (n : nat) (x : nadd) : (term82 n x B) = (term86 B n x).
Proof. exact (TRANS (@lem1263057 B n x) (@lem1263060 B n x)). Qed.
Lemma lem1263077 (B : nat) (n : nat) (x : nadd) : (term67 x n B) = (term86 B n x).
Proof. exact (TRANS (@lem1263037 n x B) (@lem1263076 B n x)). Qed.
Lemma lem1263078 (x : nadd) (n : nat) : (term53 x n) = (term53 x n).
Proof. exact (eq_refl (term53 x n)). Qed.
Lemma lem1263079 (B : nat) (n : nat) (x : nadd) : (term68 x n B) = (term87 B n x).
Proof. exact (MK_COMB (@lem1263078 x n) (@lem1263077 B n x)). Qed.
Lemma lem1263080 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1263081 (B : nat) (n : nat) (x : nadd) : (term70 x n B) = (term88 B n x).
Proof. exact (MK_COMB (@lem1263080) (@lem1263079 B n x)). Qed.
Lemma lem1263083 (m : nat) (n : nat) (p : nat) : (term89 m n p) = (term81 m n p).
Proof. exact (proj1 (@lem1262856 n m p)). Qed.
Lemma lem1263084 (x : nadd) (n : nat) (B : nat) : (term77 x n B) = (term90 x n B).
Proof. exact (@lem1263083 (Nat.mul B n) (term91 x n) B). Qed.
Lemma lem1263095 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1263096 (B : nat) (x : nadd) (n : nat) : (term92 x n B) = (term93 B x n).
Proof. exact (@lem1263095 B (term91 x n)). Qed.
Lemma lem1263101 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem1263102 (n : nat) (x : nadd) : (term91 x n) = (term41 n x).
Proof. exact (@lem1263101 n (term73 x)). Qed.
Lemma lem1263106 (B : nat) : (Nat.add B) = (Nat.add B).
Proof. exact (eq_refl (Nat.add B)). Qed.
Lemma lem1263107 (B : nat) (n : nat) (x : nadd) : (term93 B x n) = (term84 B n x).
Proof. exact (MK_COMB (@lem1263106 B) (@lem1263102 n x)). Qed.
Lemma lem1263111 (B : nat) (n : nat) (x : nadd) : (term92 x n B) = (term84 B n x).
Proof. exact (TRANS (@lem1263096 B x n) (@lem1263107 B n x)). Qed.
Lemma lem1263112 (B : nat) (n : nat) : (term64 B n) = (term64 B n).
Proof. exact (eq_refl (term64 B n)). Qed.
Lemma lem1263113 (B : nat) (n : nat) (x : nadd) : (term90 x n B) = (term85 B n x).
Proof. exact (MK_COMB (@lem1263112 B n) (@lem1263111 B n x)). Qed.
Lemma lem1263115 (n : nat) (m : nat) (p : nat) : (term81 m n p) = (term81 n m p).
Proof. exact (proj2 (@lem1262856 n m p)). Qed.
Lemma lem1263116 (B : nat) (n : nat) (x : nadd) : (term85 B n x) = (term86 B n x).
Proof. exact (@lem1263115 B (Nat.mul B n) (term41 n x)). Qed.
Lemma lem1263132 (B : nat) (n : nat) (x : nadd) : (term90 x n B) = (term86 B n x).
Proof. exact (TRANS (@lem1263113 B n x) (@lem1263116 B n x)). Qed.
Lemma lem1263133 (B : nat) (n : nat) (x : nadd) : (term77 x n B) = (term86 B n x).
Proof. exact (TRANS (@lem1263084 x n B) (@lem1263132 B n x)). Qed.
Lemma lem1263134 (x : nadd) (n : nat) : (term53 x n) = (term53 x n).
Proof. exact (eq_refl (term53 x n)). Qed.
Lemma lem1263135 (B : nat) (n : nat) (x : nadd) : (term78 x n B) = (term87 B n x).
Proof. exact (MK_COMB (@lem1263134 x n) (@lem1263133 B n x)). Qed.
Lemma lem1263136 (B : nat) (n : nat) (x : nadd) : (term80 x n B) = (term94 B n x).
Proof. exact (MK_COMB (@lem1263081 B n x) (@lem1263135 B n x)). Qed.
Lemma lem1263138 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1263139 (B : nat) (n : nat) (x : nadd) : (term94 B n x) = True.
Proof. exact (@lem1263138 (term87 B n x)). Qed.
Lemma lem1263140 (x : nadd) (n : nat) (B : nat) : (term80 x n B) = True.
Proof. exact (TRANS (@lem1263136 B n x) (@lem1263139 B n x)). Qed.
Lemma lem1263141 (x : nadd) (n : nat) (B : nat) : True = (term80 x n B).
Proof. exact (SYM (@lem1263140 x n B)). Qed.
Lemma lem1263142 (x : nadd) (n : nat) (B : nat) : term80 x n B.
Proof. exact (EQ_MP (@lem1263141 x n B) (@lem0)). Qed.
Lemma lem1263143 (x : nadd) (n : nat) (B : nat) : term79 x n B.
Proof. exact (EQ_MP (@lem1263032 x n B) (@lem1263142 x n B)). Qed.
Lemma lem1263144 (x : nadd) (B : nat) (n : nat) (h1 : term57 x B n) : term60 x n B.
Proof. exact (@lem1263143 x n B (@lem1263002 x B n h1)). Qed.
Lemma lem1263145 (x : nadd) (n : nat) (B : nat) : term62 x n B.
Proof. exact (fun h0 : term57 x B n => @lem1263144 x B n h0). Qed.
Lemma lem1263146 (x : nadd) (n : nat) (B : nat) : term61 x n B.
Proof. exact (EQ_MP (@lem1263000 x n B) (@lem1263145 x n B)). Qed.
Lemma lem1263147 (n : nat) (x : nadd) (B : nat) (h1 : term33 x B) : term60 x n B.
Proof. exact (@lem1263146 x n B (@lem1262964 n x B h1)). Qed.
Lemma lem1263152 (x : nadd) (B : nat) (h1 : term33 x B) : term95 x B.
Proof. exact (fun n : nat => @lem1263147 n x B h1). Qed.
Lemma lem1263153 (x : nadd) (B : nat) (h1 : term33 x B) : term96 B x.
Proof. exact (ex_intro (term97 B x) B (@lem1263152 x B h1)). Qed.
Lemma lem1263154 (x : nadd) (B : nat) (h1 : term33 x B) : term98 x.
Proof. exact (ex_intro (term99 x) (term100 B x) (@lem1263153 x B h1)). Qed.
Lemma lem1263155 (x : nadd) : term98 x.
Proof. exact (ex_elim (@lem1262957 x) (fun B : nat => fun h0 : term101 x B => @lem1263154 x B h0)). Qed.
Lemma lem1263160 : term102.
Proof. exact (fun x : nadd => @lem1263155 x). Qed.
