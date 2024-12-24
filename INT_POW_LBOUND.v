Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_LBOUND_term_abbrevs.
Require Import REAL_POW_LBOUND_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2308120 (x : int) : term0 x.
Proof. exact (@lem1704991 (real_of_int x)). Qed.
Lemma lem2308121 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2308122 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2308121 x) (@lem2308120 x)). Qed.
Lemma lem2308123 (x : int) (n : nat) : term2 x n.
Proof. exact (@lem2308122 x n). Qed.
Lemma lem2308124 (x : int) (n : nat) : (term2 x n) = (term3 x n).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem2308125 (x : int) (n : nat) : term3 x n.
Proof. exact (EQ_MP (@lem2308124 x n) (@lem2308123 x n)). Qed.
Lemma lem2308127 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308128 : term5 = term6.
Proof. exact (@lem2308127 (NUMERAL 0)). Qed.
Lemma lem2308129 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2308130 : term7 = term8.
Proof. exact (MK_COMB (@lem2308129) (@lem2308128)). Qed.
Lemma lem2308131 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2308132 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem2308130) (@lem2308131 x)). Qed.
Lemma lem2308134 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2308135 (x : int) : (term10 x) = (term12 x).
Proof. exact (@lem2308134 term13 x). Qed.
Lemma lem2308136 (x : int) : (term9 x) = (term12 x).
Proof. exact (TRANS (@lem2308132 x) (@lem2308135 x)). Qed.
Lemma lem2308137 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2308138 (x : int) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem2308137) (@lem2308136 x)). Qed.
Lemma lem2308140 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308141 : term16 = term17.
Proof. exact (@lem2308140 term18). Qed.
Lemma lem2308142 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2308143 : term19 = term20.
Proof. exact (MK_COMB (@lem2308142) (@lem2308141)). Qed.
Lemma lem2308145 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308146 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2308147 (n : nat) : (term21 n) = (term22 n).
Proof. exact (MK_COMB (@lem2308146) (@lem2308145 n)). Qed.
Lemma lem2308148 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2308149 (n : nat) (x : int) : (term23 n x) = (term24 n x).
Proof. exact (MK_COMB (@lem2308147 n) (@lem2308148 x)). Qed.
Lemma lem2308151 (x : int) (y : int) : (term25 x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2308152 (n : nat) (x : int) : (term24 n x) = (term27 n x).
Proof. exact (@lem2308151 (int_of_num n) x). Qed.
Lemma lem2308153 (n : nat) (x : int) : (term23 n x) = (term27 n x).
Proof. exact (TRANS (@lem2308149 n x) (@lem2308152 n x)). Qed.
Lemma lem2308154 (n : nat) (x : int) : (term28 n x) = (term29 n x).
Proof. exact (MK_COMB (@lem2308143) (@lem2308153 n x)). Qed.
Lemma lem2308156 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2308157 (n : nat) (x : int) : (term29 n x) = (term32 n x).
Proof. exact (@lem2308156 term33 (term34 n x)). Qed.
Lemma lem2308158 (n : nat) (x : int) : (term28 n x) = (term32 n x).
Proof. exact (TRANS (@lem2308154 n x) (@lem2308157 n x)). Qed.
Lemma lem2308159 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2308160 (n : nat) (x : int) : (term35 n x) = (term36 n x).
Proof. exact (MK_COMB (@lem2308159) (@lem2308158 n x)). Qed.
Lemma lem2308162 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308163 : term16 = term17.
Proof. exact (@lem2308162 term18). Qed.
Lemma lem2308164 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2308165 : term19 = term20.
Proof. exact (MK_COMB (@lem2308164) (@lem2308163)). Qed.
Lemma lem2308166 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2308167 (x : int) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem2308165) (@lem2308166 x)). Qed.
Lemma lem2308169 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2308170 (x : int) : (term38 x) = (term39 x).
Proof. exact (@lem2308169 term33 x). Qed.
Lemma lem2308171 (x : int) : (term37 x) = (term39 x).
Proof. exact (TRANS (@lem2308167 x) (@lem2308170 x)). Qed.
Lemma lem2308172 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem2308173 (x : int) : (term40 x) = (term41 x).
Proof. exact (MK_COMB (@lem2308172) (@lem2308171 x)). Qed.
Lemma lem2308174 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2308175 (x : int) (n : nat) : (term42 x n) = (term43 x n).
Proof. exact (MK_COMB (@lem2308173 x) (@lem2308174 n)). Qed.
Lemma lem2308177 (x : int) (n : nat) : (term44 x n) = (term45 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308178 (x : int) (n : nat) : (term43 x n) = (term46 x n).
Proof. exact (@lem2308177 (term47 x) n). Qed.
Lemma lem2308179 (x : int) (n : nat) : (term42 x n) = (term46 x n).
Proof. exact (TRANS (@lem2308175 x n) (@lem2308178 x n)). Qed.
Lemma lem2308180 (x : int) (n : nat) : (term48 x n) = (term49 x n).
Proof. exact (MK_COMB (@lem2308160 n x) (@lem2308179 x n)). Qed.
Lemma lem2308182 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2308183 (x : int) (n : nat) : (term49 x n) = (term50 x n).
Proof. exact (@lem2308182 (term51 n x) (term52 x n)). Qed.
Lemma lem2308184 (x : int) (n : nat) : (term48 x n) = (term50 x n).
Proof. exact (TRANS (@lem2308180 x n) (@lem2308183 x n)). Qed.
Lemma lem2308185 (x : int) (n : nat) : (term3 x n) = (term53 x n).
Proof. exact (MK_COMB (@lem2308138 x) (@lem2308184 x n)). Qed.
Lemma lem2308186 (x : int) (n : nat) : term53 x n.
Proof. exact (EQ_MP (@lem2308185 x n) (@lem2308125 x n)). Qed.
Lemma lem2308187 (x : int) : term54 x.
Proof. exact (fun n : nat => @lem2308186 x n). Qed.
Lemma lem2308188 : term55.
Proof. exact (fun x : int => @lem2308187 x). Qed.
