Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_CONG_LREM_term_abbrevs.
Require Import INT_REM_EQ_spec.
Require Import INT_REM_REM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2528104 (m : int) (n : int) (p : int) (h1 : ((rem m p) = (rem n p)) = (term0 m n p)) : ((rem m p) = (rem n p)) = (term0 m n p).
Proof. exact (h1). Qed.
Lemma lem2528105 (m : int) (n : int) (p : int) (h1 : ((rem m p) = (rem n p)) = (term0 m n p)) : (term0 m n p) = ((rem m p) = (rem n p)).
Proof. exact (SYM (@lem2528104 m n p h1)). Qed.
Lemma lem2528106 (m : int) (n : int) (p : int) (h1 : (term0 m n p) = ((rem m p) = (rem n p))) : (term0 m n p) = ((rem m p) = (rem n p)).
Proof. exact (h1). Qed.
Lemma lem2528107 (m : int) (n : int) (p : int) (h1 : (term0 m n p) = ((rem m p) = (rem n p))) : ((rem m p) = (rem n p)) = (term0 m n p).
Proof. exact (SYM (@lem2528106 m n p h1)). Qed.
Lemma lem2528108 (m : int) (n : int) (p : int) : (((rem m p) = (rem n p)) = (term0 m n p)) = ((term0 m n p) = ((rem m p) = (rem n p))).
Proof. exact (prop_ext (fun h1 : ((rem m p) = (rem n p)) = (term0 m n p) => @lem2528105 m n p h1) (fun h1 : (term0 m n p) = ((rem m p) = (rem n p)) => @lem2528107 m n p h1)). Qed.
Lemma lem2528109 (m : int) (n : int) : (term1 m n) = (term2 m n).
Proof. exact (fun_ext (fun p : int => @lem2528108 m n p)). Qed.
Lemma lem2528110 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2528111 (m : int) (n : int) : (term3 m n) = (term4 m n).
Proof. exact (MK_COMB (@lem2528110) (@lem2528109 m n)). Qed.
Lemma lem2528112 (m : int) : (term5 m) = (term6 m).
Proof. exact (fun_ext (fun n : int => @lem2528111 m n)). Qed.
Lemma lem2528113 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2528114 (m : int) : (term7 m) = (term8 m).
Proof. exact (MK_COMB (@lem2528113) (@lem2528112 m)). Qed.
Lemma lem2528115 : term9 = term10.
Proof. exact (fun_ext (fun m : int => @lem2528114 m)). Qed.
Lemma lem2528116 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2528117 : term11 = term12.
Proof. exact (MK_COMB (@lem2528116) (@lem2528115)). Qed.
Lemma lem2528118 : term12.
Proof. exact (EQ_MP (@lem2528117) (@lem2522863)). Qed.
Lemma lem2528119 (m : int) : term13 m.
Proof. exact (@lem2521244 m). Qed.
Lemma lem2528120 (m : int) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem2528121 (m : int) : term14 m.
Proof. exact (EQ_MP (@lem2528120 m) (@lem2528119 m)). Qed.
Lemma lem2528122 (m : int) (n : int) : term15 m n.
Proof. exact (@lem2528121 m n). Qed.
Lemma lem2528123 (m : int) (n : int) : (term15 m n) = ((term16 m n) = (rem m n)).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem2528125 (m : int) : term17 m.
Proof. exact (@lem2528118 m). Qed.
Lemma lem2528126 (m : int) : (term17 m) = (term8 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem2528127 (m : int) : term8 m.
Proof. exact (EQ_MP (@lem2528126 m) (@lem2528125 m)). Qed.
Lemma lem2528128 (m : int) (n : int) : term18 m n.
Proof. exact (@lem2528127 m n). Qed.
Lemma lem2528129 (m : int) (n : int) : (term18 m n) = (term4 m n).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem2528130 (m : int) (n : int) : term4 m n.
Proof. exact (EQ_MP (@lem2528129 m n) (@lem2528128 m n)). Qed.
Lemma lem2528131 (m : int) (n : int) (p : int) : term19 m n p.
Proof. exact (@lem2528130 m n p). Qed.
Lemma lem2528132 (m : int) (n : int) (p : int) : (term19 m n p) = ((term0 m n p) = ((rem m p) = (rem n p))).
Proof. exact (eq_refl (term19 m n p)). Qed.
Lemma lem2528149 (m : int) (n : int) (p : int) : (term0 m n p) = ((rem m p) = (rem n p)).
Proof. exact (EQ_MP (@lem2528132 m n p) (@lem2528131 m n p)). Qed.
Lemma lem2528150 (x : int) (y : int) (n : int) : (term20 x y n) = ((term16 x n) = (rem y n)).
Proof. exact (@lem2528149 (rem x n) y n). Qed.
Lemma lem2528154 (m : int) (n : int) : (term16 m n) = (rem m n).
Proof. exact (EQ_MP (@lem2528123 m n) (@lem2528122 m n)). Qed.
Lemma lem2528155 (x : int) (n : int) : (term16 x n) = (rem x n).
Proof. exact (@lem2528154 x n). Qed.
Lemma lem2528156 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2528157 (x : int) (n : int) : (term21 x n) = (term22 x n).
Proof. exact (MK_COMB (@lem2528156) (@lem2528155 x n)). Qed.
Lemma lem2528158 (y : int) (n : int) : (rem y n) = (rem y n).
Proof. exact (eq_refl (rem y n)). Qed.
Lemma lem2528159 (x : int) (y : int) (n : int) : ((term16 x n) = (rem y n)) = ((rem x n) = (rem y n)).
Proof. exact (MK_COMB (@lem2528157 x n) (@lem2528158 y n)). Qed.
Lemma lem2528162 (x : int) (y : int) (n : int) : (term20 x y n) = ((rem x n) = (rem y n)).
Proof. exact (TRANS (@lem2528150 x y n) (@lem2528159 x y n)). Qed.
Lemma lem2528163 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2528164 (x : int) (y : int) (n : int) : (term23 x y n) = (term24 x y n).
Proof. exact (MK_COMB (@lem2528163) (@lem2528162 x y n)). Qed.
Lemma lem2528166 (m : int) (n : int) (p : int) : (term0 m n p) = ((rem m p) = (rem n p)).
Proof. exact (EQ_MP (@lem2528132 m n p) (@lem2528131 m n p)). Qed.
Lemma lem2528167 (x : int) (y : int) (n : int) : (term0 x y n) = ((rem x n) = (rem y n)).
Proof. exact (@lem2528166 x y n). Qed.
Lemma lem2528170 (x : int) (y : int) (n : int) : ((term20 x y n) = (term0 x y n)) = (((rem x n) = (rem y n)) = ((rem x n) = (rem y n))).
Proof. exact (MK_COMB (@lem2528164 x y n) (@lem2528167 x y n)). Qed.
Lemma lem2528172 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2528173 (x : Prop) : (x = x) = True.
Proof. exact (@lem2528172 Prop x). Qed.
Lemma lem2528174 (x : int) (y : int) (n : int) : (((rem x n) = (rem y n)) = ((rem x n) = (rem y n))) = True.
Proof. exact (@lem2528173 ((rem x n) = (rem y n))). Qed.
Lemma lem2528175 (x : int) (y : int) (n : int) : ((term20 x y n) = (term0 x y n)) = True.
Proof. exact (TRANS (@lem2528170 x y n) (@lem2528174 x y n)). Qed.
Lemma lem2528176 (x : int) (y : int) : (term25 x y) = term26.
Proof. exact (fun_ext (fun n : int => @lem2528175 x y n)). Qed.
Lemma lem2528177 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2528178 (x : int) (y : int) : (term27 x y) = term28.
Proof. exact (MK_COMB (@lem2528177) (@lem2528176 x y)). Qed.
Lemma lem2528180 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2528181 (t : Prop) : (term30 t) = t.
Proof. exact (@lem2528180 int t). Qed.
Lemma lem2528182 : term28 = True.
Proof. exact (@lem2528181 True). Qed.
Lemma lem2528183 (x : int) (y : int) : (term27 x y) = True.
Proof. exact (TRANS (@lem2528178 x y) (@lem2528182)). Qed.
Lemma lem2528184 (x : int) : (term31 x) = term26.
Proof. exact (fun_ext (fun y : int => @lem2528183 x y)). Qed.
Lemma lem2528185 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2528186 (x : int) : (term32 x) = term28.
Proof. exact (MK_COMB (@lem2528185) (@lem2528184 x)). Qed.
Lemma lem2528188 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2528189 (t : Prop) : (term30 t) = t.
Proof. exact (@lem2528188 int t). Qed.
Lemma lem2528190 : term28 = True.
Proof. exact (@lem2528189 True). Qed.
Lemma lem2528191 (x : int) : (term32 x) = True.
Proof. exact (TRANS (@lem2528186 x) (@lem2528190)). Qed.
Lemma lem2528192 : term33 = term26.
Proof. exact (fun_ext (fun x : int => @lem2528191 x)). Qed.
Lemma lem2528193 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2528194 : term34 = term28.
Proof. exact (MK_COMB (@lem2528193) (@lem2528192)). Qed.
Lemma lem2528196 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2528197 (t : Prop) : (term30 t) = t.
Proof. exact (@lem2528196 int t). Qed.
Lemma lem2528198 : term28 = True.
Proof. exact (@lem2528197 True). Qed.
Lemma lem2528199 : term34 = True.
Proof. exact (TRANS (@lem2528194) (@lem2528198)). Qed.
Lemma lem2528200 : True = term34.
Proof. exact (SYM (@lem2528199)). Qed.
Lemma lem2528201 : term34.
Proof. exact (EQ_MP (@lem2528200) (@lem0)). Qed.
