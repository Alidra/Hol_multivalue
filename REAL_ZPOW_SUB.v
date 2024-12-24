Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ZPOW_SUB_term_abbrevs.
Require Import INT_SUB_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_ZPOW_ADD_spec.
Require Import REAL_ZPOW_NEG_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem3179020 (x : real) : term0 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem3179021 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem3179022 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem3179021 x) (@lem3179020 x)). Qed.
Lemma lem3179023 (x : real) (y : real) : term2 x y.
Proof. exact (@lem3179022 x y). Qed.
Lemma lem3179024 (x : real) (y : real) : (term2 x y) = ((real_div x y) = (term3 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem3179026 (x : real) : term4 x.
Proof. exact (@lem3173052 x). Qed.
Lemma lem3179027 (x : real) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem3179028 (x : real) : term5 x.
Proof. exact (EQ_MP (@lem3179027 x) (@lem3179026 x)). Qed.
Lemma lem3179029 (x : real) (n : int) : term6 x n.
Proof. exact (@lem3179028 x n). Qed.
Lemma lem3179030 (x : real) (n : int) : (term6 x n) = ((term7 x n) = (term8 x n)).
Proof. exact (eq_refl (term6 x n)). Qed.
Lemma lem3179032 (x : real) : term9 x.
Proof. exact (@lem3179019 x). Qed.
Lemma lem3179033 (x : real) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem3179034 (x : real) : term10 x.
Proof. exact (EQ_MP (@lem3179033 x) (@lem3179032 x)). Qed.
Lemma lem3179035 (x : real) (m : int) : term11 x m.
Proof. exact (@lem3179034 x m). Qed.
Lemma lem3179036 (m : int) (x : real) : (term11 x m) = (term12 m x).
Proof. exact (eq_refl (term11 x m)). Qed.
Lemma lem3179037 (m : int) (x : real) : term12 m x.
Proof. exact (EQ_MP (@lem3179036 m x) (@lem3179035 x m)). Qed.
Lemma lem3179038 (m : int) (x : real) (n : int) : term13 m x n.
Proof. exact (@lem3179037 m x n). Qed.
Lemma lem3179039 (m : int) (x : real) (n : int) : (term13 m x n) = (term14 m x n).
Proof. exact (eq_refl (term13 m x n)). Qed.
Lemma lem3179040 (m : int) (x : real) (n : int) : term14 m x n.
Proof. exact (EQ_MP (@lem3179039 m x n) (@lem3179038 m x n)). Qed.
Lemma lem3179041 (x : real) (h1 : term15 x) : term15 x.
Proof. exact (h1). Qed.
Lemma lem3179042 (m : int) (n : int) (x : real) (h1 : term15 x) : (term16 x m n) = (term17 m x n).
Proof. exact (@lem3179040 m x n (@lem3179041 x h1)). Qed.
Lemma lem3179048 (x : int) : term18 x.
Proof. exact (@lem2319812 x). Qed.
Lemma lem3179049 (x : int) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem3179050 (x : int) : term19 x.
Proof. exact (EQ_MP (@lem3179049 x) (@lem3179048 x)). Qed.
Lemma lem3179051 (x : int) (y : int) : term20 x y.
Proof. exact (@lem3179050 x y). Qed.
Lemma lem3179052 (x : int) (y : int) : (term20 x y) = ((int_sub x y) = (term21 x y)).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem3179069 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term22 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3179070 (p : Prop) (q : Prop) (p' : Prop) : term23 p q p'.
Proof. exact (fun q' : Prop => @lem3179069 p q p' q'). Qed.
Lemma lem3179071 (p : Prop) (q : Prop) : term24 p q.
Proof. exact (fun p' : Prop => @lem3179070 p q p'). Qed.
Lemma lem3179072 (m : int) (x : real) (n : int) : term25 m x n.
Proof. exact (@lem3179071 (term15 x) ((term26 x m n) = (term27 m x n))). Qed.
Lemma lem3179073 (m : int) (x : real) (n : int) (p' : Prop) : term28 m x n p'.
Proof. exact (@lem3179072 m x n p'). Qed.
Lemma lem3179074 (m : int) (x : real) (n : int) (p' : Prop) : (term28 m x n p') = (term29 m x n p').
Proof. exact (eq_refl (term28 m x n p')). Qed.
Lemma lem3179075 (m : int) (x : real) (n : int) (p' : Prop) : term29 m x n p'.
Proof. exact (EQ_MP (@lem3179074 m x n p') (@lem3179073 m x n p')). Qed.
Lemma lem3179076 (m : int) (x : real) (n : int) (p' : Prop) (q' : Prop) : term30 m x n p' q'.
Proof. exact (@lem3179075 m x n p' q'). Qed.
Lemma lem3179077 (m : int) (x : real) (n : int) (p' : Prop) (q' : Prop) : (term30 m x n p' q') = (term31 m x n p' q').
Proof. exact (eq_refl (term30 m x n p' q')). Qed.
Lemma lem3179078 (m : int) (x : real) (n : int) (p' : Prop) (q' : Prop) : term31 m x n p' q'.
Proof. exact (EQ_MP (@lem3179077 m x n p' q') (@lem3179076 m x n p' q')). Qed.
Lemma lem3179081 (x : real) : (term15 x) = (term15 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem3179082 (m : int) (n : int) (x : real) (q' : Prop) : term32 m n x q'.
Proof. exact (@lem3179078 m x n (term15 x) q'). Qed.
Lemma lem3179083 (m : int) (n : int) (x : real) (q' : Prop) : term33 m n x q'.
Proof. exact (@lem3179082 m n x q' (@lem3179081 x)). Qed.
Lemma lem3179084 (x : real) (h1 : term15 x) : term15 x.
Proof. exact (h1). Qed.
Lemma lem3179085 (x : real) : term34 x.
Proof. exact (@lem82 (x = term35)). Qed.
Lemma lem3179101 (x : int) (y : int) : (int_sub x y) = (term21 x y).
Proof. exact (EQ_MP (@lem3179052 x y) (@lem3179051 x y)). Qed.
Lemma lem3179102 (m : int) (n : int) : (int_sub m n) = (term21 m n).
Proof. exact (@lem3179101 m n). Qed.
Lemma lem3179103 (x : real) : (real_zpow x) = (real_zpow x).
Proof. exact (eq_refl (real_zpow x)). Qed.
Lemma lem3179104 (x : real) (m : int) (n : int) : (term26 x m n) = (term36 x m n).
Proof. exact (MK_COMB (@lem3179103 x) (@lem3179102 m n)). Qed.
Lemma lem3179106 (m : int) (x : real) (n : int) : term14 m x n.
Proof. exact (fun h0 : term15 x => @lem3179042 m n x h0). Qed.
Lemma lem3179107 (m : int) (x : real) (n : int) : term37 m x n.
Proof. exact (@lem3179106 m x (int_neg n)). Qed.
Lemma lem3179109 (x : real) (h1 : term15 x) : (x = term35) = False.
Proof. exact (@lem3179085 x (@lem3179084 x h1)). Qed.
Lemma lem3179110 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3179111 (x : real) (h1 : term15 x) : (term15 x) = (~ False).
Proof. exact (MK_COMB (@lem3179110) (@lem3179109 x h1)). Qed.
Lemma lem3179113 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3179114 (x : real) (h1 : term15 x) : (term15 x) = True.
Proof. exact (TRANS (@lem3179111 x h1) (@lem3179113)). Qed.
Lemma lem3179115 (x : real) (h1 : term15 x) : True = (term15 x).
Proof. exact (SYM (@lem3179114 x h1)). Qed.
Lemma lem3179116 (x : real) (h1 : term15 x) : term15 x.
Proof. exact (EQ_MP (@lem3179115 x h1) (@lem0)). Qed.
Lemma lem3179117 (m : int) (n : int) (x : real) (h1 : term15 x) : (term36 x m n) = (term38 m x n).
Proof. exact (@lem3179107 m x n (@lem3179116 x h1)). Qed.
Lemma lem3179119 (x : real) (n : int) : (term7 x n) = (term8 x n).
Proof. exact (EQ_MP (@lem3179030 x n) (@lem3179029 x n)). Qed.
Lemma lem3179120 (x : real) (m : int) : (term39 x m) = (term39 x m).
Proof. exact (eq_refl (term39 x m)). Qed.
Lemma lem3179121 (m : int) (x : real) (n : int) : (term38 m x n) = (term40 m x n).
Proof. exact (MK_COMB (@lem3179120 x m) (@lem3179119 x n)). Qed.
Lemma lem3179122 (m : int) (n : int) (x : real) (h1 : term15 x) : (term36 x m n) = (term40 m x n).
Proof. exact (TRANS (@lem3179117 m n x h1) (@lem3179121 m x n)). Qed.
Lemma lem3179123 (m : int) (n : int) (x : real) (h1 : term15 x) : (term26 x m n) = (term40 m x n).
Proof. exact (TRANS (@lem3179104 x m n) (@lem3179122 m n x h1)). Qed.
Lemma lem3179124 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3179125 (m : int) (n : int) (x : real) (h1 : term15 x) : (term41 x m n) = (term42 m x n).
Proof. exact (MK_COMB (@lem3179124) (@lem3179123 m n x h1)). Qed.
Lemma lem3179127 (x : real) (y : real) : (real_div x y) = (term3 x y).
Proof. exact (EQ_MP (@lem3179024 x y) (@lem3179023 x y)). Qed.
Lemma lem3179128 (m : int) (x : real) (n : int) : (term27 m x n) = (term40 m x n).
Proof. exact (@lem3179127 (real_zpow x m) (real_zpow x n)). Qed.
Lemma lem3179129 (m : int) (n : int) (x : real) (h1 : term15 x) : ((term26 x m n) = (term27 m x n)) = ((term40 m x n) = (term40 m x n)).
Proof. exact (MK_COMB (@lem3179125 m n x h1) (@lem3179128 m x n)). Qed.
Lemma lem3179131 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3179132 (x : real) : (x = x) = True.
Proof. exact (@lem3179131 real x). Qed.
Lemma lem3179133 (m : int) (x : real) (n : int) : ((term40 m x n) = (term40 m x n)) = True.
Proof. exact (@lem3179132 (term40 m x n)). Qed.
Lemma lem3179134 (m : int) (n : int) (x : real) (h1 : term15 x) : ((term26 x m n) = (term27 m x n)) = True.
Proof. exact (TRANS (@lem3179129 m n x h1) (@lem3179133 m x n)). Qed.
Lemma lem3179135 (m : int) (x : real) (n : int) : term43 m x n.
Proof. exact (fun h0 : term15 x => @lem3179134 m n x h0). Qed.
Lemma lem3179136 (m : int) (n : int) (x : real) : term44 m n x.
Proof. exact (@lem3179083 m n x True). Qed.
Lemma lem3179137 (m : int) (n : int) (x : real) : (term45 m x n) = (term46 x).
Proof. exact (@lem3179136 m n x (@lem3179135 m x n)). Qed.
Lemma lem3179139 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3179140 (x : real) : (term46 x) = True.
Proof. exact (@lem3179139 (term15 x)). Qed.
Lemma lem3179141 (m : int) (x : real) (n : int) : (term45 m x n) = True.
Proof. exact (TRANS (@lem3179137 m n x) (@lem3179140 x)). Qed.
Lemma lem3179142 (m : int) (x : real) : (term47 m x) = term48.
Proof. exact (fun_ext (fun n : int => @lem3179141 m x n)). Qed.
Lemma lem3179143 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3179144 (m : int) (x : real) : (term49 m x) = term50.
Proof. exact (MK_COMB (@lem3179143) (@lem3179142 m x)). Qed.
Lemma lem3179146 {A : Type'} (t : Prop) : (term51 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3179147 (t : Prop) : (term52 t) = t.
Proof. exact (@lem3179146 int t). Qed.
Lemma lem3179148 : term50 = True.
Proof. exact (@lem3179147 True). Qed.
Lemma lem3179149 (m : int) (x : real) : (term49 m x) = True.
Proof. exact (TRANS (@lem3179144 m x) (@lem3179148)). Qed.
Lemma lem3179150 (x : real) : (term53 x) = term48.
Proof. exact (fun_ext (fun m : int => @lem3179149 m x)). Qed.
Lemma lem3179151 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3179152 (x : real) : (term54 x) = term50.
Proof. exact (MK_COMB (@lem3179151) (@lem3179150 x)). Qed.
Lemma lem3179154 {A : Type'} (t : Prop) : (term51 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3179155 (t : Prop) : (term52 t) = t.
Proof. exact (@lem3179154 int t). Qed.
Lemma lem3179156 : term50 = True.
Proof. exact (@lem3179155 True). Qed.
Lemma lem3179157 (x : real) : (term54 x) = True.
Proof. exact (TRANS (@lem3179152 x) (@lem3179156)). Qed.
Lemma lem3179158 : term55 = term56.
Proof. exact (fun_ext (fun x : real => @lem3179157 x)). Qed.
Lemma lem3179159 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3179160 : term57 = term58.
Proof. exact (MK_COMB (@lem3179159) (@lem3179158)). Qed.
Lemma lem3179162 {A : Type'} (t : Prop) : (term51 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3179163 (t : Prop) : (term59 t) = t.
Proof. exact (@lem3179162 real t). Qed.
Lemma lem3179164 : term58 = True.
Proof. exact (@lem3179163 True). Qed.
Lemma lem3179165 : term57 = True.
Proof. exact (TRANS (@lem3179160) (@lem3179164)). Qed.
Lemma lem3179166 : True = term57.
Proof. exact (SYM (@lem3179165)). Qed.
Lemma lem3179167 : term57.
Proof. exact (EQ_MP (@lem3179166) (@lem0)). Qed.
