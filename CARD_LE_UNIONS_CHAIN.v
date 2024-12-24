Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_LE_UNIONS_CHAIN_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import CARD_CLAUSES_spec.
Require Import CHOOSE_SUBSET_EQ_spec.
Require Import CONTRAPOS_THM_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINITE_EMPTY_spec.
Require Import FINITE_SUBSET_UNIONS_CHAIN_spec.
Require Import HAS_SIZE_spec.
Require Import INT_POS_spec.
Require Import LE_0_spec.
Require Import MONO_EXISTS_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_FORALL_THM_spec.
Require Import NOT_IMP_spec.
Require Import RIGHT_AND_EXISTS_THM_spec.
Require Import SWAP_EXISTS_THM_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm16485_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm17500_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841416_spec.
Require Import thm2841417_spec.
Require Import thm3322101_spec.
Require Import thm3322164_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem4106043 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem4106044 {A : Type'} (f : type686 A) (h1 : term0 A) : term1 A f.
Proof. exact (@lem4106043 A h1 f). Qed.
Lemma lem4106045 {A : Type'} (f : type686 A) : (term1 A f) = (term2 A f).
Proof. exact (eq_refl (term1 A f)). Qed.
Lemma lem4106046 {A : Type'} (f : type686 A) (h1 : term0 A) : term2 A f.
Proof. exact (EQ_MP (@lem4106045 A f) (@lem4106044 A f h1)). Qed.
Lemma lem4106047 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term0 A) : term3 A f s.
Proof. exact (@lem4106046 A f h1 s). Qed.
Lemma lem4106048 {A : Type'} (f : type686 A) (s : A -> Prop) : (term3 A f s) = (term4 A f s).
Proof. exact (eq_refl (term3 A f s)). Qed.
Lemma lem4106049 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term0 A) : term4 A f s.
Proof. exact (EQ_MP (@lem4106048 A f s) (@lem4106047 A f s h1)). Qed.
Lemma lem4106050 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term5 A s f) : term5 A s f.
Proof. exact (h1). Qed.
Lemma lem4106051 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term0 A) (h2 : term5 A s f) : term6 A f s.
Proof. exact (@lem4106049 A f s h1 (@lem4106050 A s f h2)). Qed.
Lemma lem4106052 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term5 A s f) : term7 A f s.
Proof. exact (fun h0 : term0 A => @lem4106051 A s f h0 h1). Qed.
Lemma lem4106053 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem4106054 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term0 A) (h2 : term5 A s f) : term6 A f s.
Proof. exact (@lem4106052 A s f h2 (@lem4106053 A h1)). Qed.
Lemma lem4106055 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term0 A) : term4 A f s.
Proof. exact (fun h0 : term5 A s f => @lem4106054 A s f h1 h0). Qed.
Lemma lem4106056 {A : Type'} (f : type686 A) (h1 : term0 A) : term2 A f.
Proof. exact (fun s : A -> Prop => @lem4106055 A f s h1). Qed.
Lemma lem4106057 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun f : type686 A => @lem4106056 A f h1). Qed.
Lemma lem4106058 {A : Type'} : term8 A.
Proof. exact (fun h0 : term0 A => @lem4106057 A h0). Qed.
Lemma lem4106059 {A : Type'} : term0 A.
Proof. exact (@lem4106058 A (@lem3789348 A)). Qed.
Lemma lem4106060 {A : Type'} (f : type686 A) : term1 A f.
Proof. exact (@lem4106059 A f). Qed.
Lemma lem4106061 {A : Type'} (f : type686 A) : (term1 A f) = (term2 A f).
Proof. exact (eq_refl (term1 A f)). Qed.
Lemma lem4106062 {A : Type'} (f : type686 A) : term2 A f.
Proof. exact (EQ_MP (@lem4106061 A f) (@lem4106060 A f)). Qed.
Lemma lem4106063 {A : Type'} (f : type686 A) (s : A -> Prop) : term3 A f s.
Proof. exact (@lem4106062 A f s). Qed.
Lemma lem4106064 {A : Type'} (f : type686 A) (s : A -> Prop) : (term3 A f s) = (term4 A f s).
Proof. exact (eq_refl (term3 A f s)). Qed.
Lemma lem4106066 {_100044 : Type'} (s : _100044 -> Prop) : term9 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem4106067 {_100044 : Type'} (s : _100044 -> Prop) : (term9 _100044 s) = (term10 _100044 s).
Proof. exact (eq_refl (term9 _100044 s)). Qed.
Lemma lem4106068 {_100044 : Type'} (s : _100044 -> Prop) : term10 _100044 s.
Proof. exact (EQ_MP (@lem4106067 _100044 s) (@lem4106066 _100044 s)). Qed.
Lemma lem4106069 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term11 _100044 s n.
Proof. exact (@lem4106068 _100044 s n). Qed.
Lemma lem4106070 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term11 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term12 _100044 s n)).
Proof. exact (eq_refl (term11 _100044 s n)). Qed.
Lemma lem4106072 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term13 A P Q) : term13 A P Q.
Proof. exact (h1). Qed.
Lemma lem4106073 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term14 A P Q) : term14 A P Q.
Proof. exact (h1). Qed.
Lemma lem4106074 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term14 A P Q) (h2 : term13 A P Q) : term15 A P Q.
Proof. exact (@lem4106072 A P Q h2 (@lem4106073 A P Q h1)). Qed.
Lemma lem4106075 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term14 A P Q) : term16 A P Q.
Proof. exact (fun h0 : term13 A P Q => @lem4106074 A P Q h1 h0). Qed.
Lemma lem4106076 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term13 A P Q) : term13 A P Q.
Proof. exact (h1). Qed.
Lemma lem4106077 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term14 A P Q) (h2 : term13 A P Q) : term15 A P Q.
Proof. exact (@lem4106075 A P Q h1 (@lem4106076 A P Q h2)). Qed.
Lemma lem4106078 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term13 A P Q) : term13 A P Q.
Proof. exact (fun h0 : term14 A P Q => @lem4106077 A P Q h0 h1). Qed.
Lemma lem4106079 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term17 A P Q.
Proof. exact (fun h0 : term13 A P Q => @lem4106078 A P Q h0). Qed.
Lemma lem4106081 {A B : Type'} (P : type1413 A B) : term18 A B P.
Proof. exact (@lem4848 A B P). Qed.
Lemma lem4106082 {A B : Type'} (P : type1413 A B) : (term18 A B P) = ((term19 A B P) = (term20 A B P)).
Proof. exact (eq_refl (term18 A B P)). Qed.
Lemma lem4106084 {A : Type'} (P : Prop) : term21 A P.
Proof. exact (@lem5950 A P). Qed.
Lemma lem4106085 {A : Type'} (P : Prop) : (term21 A P) = (term22 A P).
Proof. exact (eq_refl (term21 A P)). Qed.
Lemma lem4106086 {A : Type'} (P : Prop) : term22 A P.
Proof. exact (EQ_MP (@lem4106085 A P) (@lem4106084 A P)). Qed.
Lemma lem4106087 {A : Type'} (P : Prop) (Q : A -> Prop) : term23 A P Q.
Proof. exact (@lem4106086 A P Q). Qed.
Lemma lem4106088 {A : Type'} (P : Prop) (Q : A -> Prop) : (term23 A P Q) = ((term24 A P Q) = (term25 A P Q)).
Proof. exact (eq_refl (term23 A P Q)). Qed.
Lemma lem4106090 {A : Type'} (n : nat) : term26 A n.
Proof. exact (@lem4085033 A n). Qed.
Lemma lem4106091 {A : Type'} (n : nat) : (term26 A n) = (term27 A n).
Proof. exact (eq_refl (term26 A n)). Qed.
Lemma lem4106092 {A : Type'} (n : nat) : term27 A n.
Proof. exact (EQ_MP (@lem4106091 A n) (@lem4106090 A n)). Qed.
Lemma lem4106093 {A : Type'} (n : nat) (s : A -> Prop) : term28 A n s.
Proof. exact (@lem4106092 A n s). Qed.
Lemma lem4106094 {A : Type'} (s : A -> Prop) (n : nat) : (term28 A n s) = ((term29 A n s) = (term30 A s n)).
Proof. exact (eq_refl (term28 A n s)). Qed.
Lemma lem4106110 (x : nat) (n : nat) : (term31 x n) = (Peano.le x n).
Proof. exact (@lem16933 (Peano.le x n)). Qed.
Lemma lem4106111 (n : nat) (x : nat) : (term32 n x) = (term32 n x).
Proof. exact (eq_refl (term32 n x)). Qed.
Lemma lem4106113 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4106114 (x : nat) (n : nat) : (term33 x n) = (term34 x n).
Proof. exact (MK_COMB (@lem4106113) (@lem4106110 x n)). Qed.
Lemma lem4106115 (n : nat) (x : nat) : (term35 n x) = (term36 n x).
Proof. exact (MK_COMB (@lem4106114 x n) (@lem4106111 n x)). Qed.
Lemma lem4106120 (n : nat) (x : nat) : (term37 n x) = (term37 n x).
Proof. exact (eq_refl (term37 n x)). Qed.
Lemma lem4106121 (n : nat) (x : nat) : (term38 n x) = (term39 n x).
Proof. exact (MK_COMB (@lem4106120 n x) (@lem4106115 n x)). Qed.
Lemma lem4106122 (n : nat) (x : nat) : ((term40 x n) = (term41 n x)) = (term38 n x).
Proof. exact (@lem17500 (term40 x n) (term41 n x)). Qed.
Lemma lem4106136 (n : nat) (x : nat) : ((term40 x n) = (term41 n x)) = (term39 n x).
Proof. exact (TRANS (@lem4106122 n x) (@lem4106121 n x)). Qed.
Lemma lem4106138 (m : nat) : (S m) = (term42 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem4106139 (n : nat) : (S n) = (term42 n).
Proof. exact (@lem4106138 n). Qed.
Lemma lem4106140 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4106141 (n : nat) : (term43 n) = (term44 n).
Proof. exact (MK_COMB (@lem4106140) (@lem4106139 n)). Qed.
Lemma lem4106142 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4106143 (n : nat) (x : nat) : (term41 n x) = (term45 n x).
Proof. exact (MK_COMB (@lem4106141 n) (@lem4106142 x)). Qed.
Lemma lem4106144 (x : nat) (n : nat) : (term46 x n) = (term46 x n).
Proof. exact (eq_refl (term46 x n)). Qed.
Lemma lem4106145 (n : nat) (x : nat) : (term47 n x) = (term48 n x).
Proof. exact (MK_COMB (@lem4106144 x n) (@lem4106143 n x)). Qed.
Lemma lem4106146 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4106147 (n : nat) (x : nat) : (term37 n x) = (term49 n x).
Proof. exact (MK_COMB (@lem4106146) (@lem4106145 n x)). Qed.
Lemma lem4106149 (m : nat) : (S m) = (term42 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem4106150 (n : nat) : (S n) = (term42 n).
Proof. exact (@lem4106149 n). Qed.
Lemma lem4106151 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4106152 (n : nat) : (term43 n) = (term44 n).
Proof. exact (MK_COMB (@lem4106151) (@lem4106150 n)). Qed.
Lemma lem4106153 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4106154 (n : nat) (x : nat) : (term41 n x) = (term45 n x).
Proof. exact (MK_COMB (@lem4106152 n) (@lem4106153 x)). Qed.
Lemma lem4106155 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4106156 (n : nat) (x : nat) : (term32 n x) = (term50 n x).
Proof. exact (MK_COMB (@lem4106155) (@lem4106154 n x)). Qed.
Lemma lem4106157 (x : nat) (n : nat) : (term34 x n) = (term34 x n).
Proof. exact (eq_refl (term34 x n)). Qed.
Lemma lem4106158 (n : nat) (x : nat) : (term36 n x) = (term51 n x).
Proof. exact (MK_COMB (@lem4106157 x n) (@lem4106156 n x)). Qed.
Lemma lem4106159 (n : nat) (x : nat) : (term39 n x) = (term52 n x).
Proof. exact (MK_COMB (@lem4106147 n x) (@lem4106158 n x)). Qed.
Lemma lem4106208 (n : nat) (x : nat) : ((term40 x n) = (term41 n x)) = (term52 n x).
Proof. exact (TRANS (@lem4106136 n x) (@lem4106159 n x)). Qed.
Lemma lem4106210 (m : nat) (n : nat) : (Peano.le m n) = (term53 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem4106211 (x : nat) (n : nat) : (Peano.le x n) = (term53 x n).
Proof. exact (@lem4106210 x n). Qed.
Lemma lem4106212 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4106213 (x : nat) (n : nat) : (term40 x n) = (term54 x n).
Proof. exact (MK_COMB (@lem4106212) (@lem4106211 x n)). Qed.
Lemma lem4106214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4106215 (x : nat) (n : nat) : (term46 x n) = (term55 x n).
Proof. exact (MK_COMB (@lem4106214) (@lem4106213 x n)). Qed.
Lemma lem4106217 (m : nat) (n : nat) : (Peano.le m n) = (term53 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem4106218 (n : nat) (x : nat) : (term45 n x) = (term56 n x).
Proof. exact (@lem4106217 (term42 n) x). Qed.
Lemma lem4106220 (m : nat) (n : nat) : (term57 m n) = (term58 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem4106221 (n : nat) : (term59 n) = (term60 n).
Proof. exact (@lem4106220 n term61). Qed.
Lemma lem4106222 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem4106223 (n : nat) : (term62 n) = (term63 n).
Proof. exact (MK_COMB (@lem4106222) (@lem4106221 n)). Qed.
Lemma lem4106224 (x : nat) : (int_of_num x) = (int_of_num x).
Proof. exact (eq_refl (int_of_num x)). Qed.
Lemma lem4106225 (n : nat) (x : nat) : (term56 n x) = (term64 n x).
Proof. exact (MK_COMB (@lem4106223 n) (@lem4106224 x)). Qed.
Lemma lem4106226 (n : nat) (x : nat) : (term45 n x) = (term64 n x).
Proof. exact (TRANS (@lem4106218 n x) (@lem4106225 n x)). Qed.
Lemma lem4106227 (n : nat) (x : nat) : (term48 n x) = (term65 n x).
Proof. exact (MK_COMB (@lem4106215 x n) (@lem4106226 n x)). Qed.
Lemma lem4106228 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4106229 (n : nat) (x : nat) : (term49 n x) = (term66 n x).
Proof. exact (MK_COMB (@lem4106228) (@lem4106227 n x)). Qed.
Lemma lem4106231 (m : nat) (n : nat) : (Peano.le m n) = (term53 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem4106232 (x : nat) (n : nat) : (Peano.le x n) = (term53 x n).
Proof. exact (@lem4106231 x n). Qed.
Lemma lem4106233 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4106234 (x : nat) (n : nat) : (term34 x n) = (term67 x n).
Proof. exact (MK_COMB (@lem4106233) (@lem4106232 x n)). Qed.
Lemma lem4106236 (m : nat) (n : nat) : (Peano.le m n) = (term53 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem4106237 (n : nat) (x : nat) : (term45 n x) = (term56 n x).
Proof. exact (@lem4106236 (term42 n) x). Qed.
Lemma lem4106239 (m : nat) (n : nat) : (term57 m n) = (term58 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem4106240 (n : nat) : (term59 n) = (term60 n).
Proof. exact (@lem4106239 n term61). Qed.
Lemma lem4106241 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem4106242 (n : nat) : (term62 n) = (term63 n).
Proof. exact (MK_COMB (@lem4106241) (@lem4106240 n)). Qed.
Lemma lem4106243 (x : nat) : (int_of_num x) = (int_of_num x).
Proof. exact (eq_refl (int_of_num x)). Qed.
Lemma lem4106244 (n : nat) (x : nat) : (term56 n x) = (term64 n x).
Proof. exact (MK_COMB (@lem4106242 n) (@lem4106243 x)). Qed.
Lemma lem4106245 (n : nat) (x : nat) : (term45 n x) = (term64 n x).
Proof. exact (TRANS (@lem4106237 n x) (@lem4106244 n x)). Qed.
Lemma lem4106246 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4106247 (n : nat) (x : nat) : (term50 n x) = (term68 n x).
Proof. exact (MK_COMB (@lem4106246) (@lem4106245 n x)). Qed.
Lemma lem4106248 (n : nat) (x : nat) : (term51 n x) = (term69 n x).
Proof. exact (MK_COMB (@lem4106234 x n) (@lem4106247 n x)). Qed.
Lemma lem4106249 (n : nat) (x : nat) : (term52 n x) = (term70 n x).
Proof. exact (MK_COMB (@lem4106229 n x) (@lem4106248 n x)). Qed.
Lemma lem4106250 (n : nat) (x : nat) : ((term40 x n) = (term41 n x)) = (term70 n x).
Proof. exact (TRANS (@lem4106208 n x) (@lem4106249 n x)). Qed.
Lemma lem4106251 (n : nat) : term71 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem4106252 (n : nat) : (term71 n) = (term72 n).
Proof. exact (eq_refl (term71 n)). Qed.
Lemma lem4106253 (n : nat) : term72 n.
Proof. exact (EQ_MP (@lem4106252 n) (@lem4106251 n)). Qed.
Lemma lem4106254 (x : nat) : term71 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem4106255 (x : nat) : (term71 x) = (term72 x).
Proof. exact (eq_refl (term71 x)). Qed.
Lemma lem4106256 (x : nat) : term72 x.
Proof. exact (EQ_MP (@lem4106255 x) (@lem4106254 x)). Qed.
Lemma lem4106257 (_48286 : int) (_48287 : int) : (term73 _48286 _48287) = (term74 _48286 _48287).
Proof. exact (@lem2318604 (term74 _48286 _48287)). Qed.
Lemma lem4106277 (_48287 : int) (_48286 : int) : (term75 _48287 _48286) = (int_le _48287 _48286).
Proof. exact (@lem16933 (int_le _48287 _48286)). Qed.
Lemma lem4106278 (_48286 : int) (_48287 : int) : (term76 _48286 _48287) = (term76 _48286 _48287).
Proof. exact (eq_refl (term76 _48286 _48287)). Qed.
Lemma lem4106279 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4106280 (_48287 : int) (_48286 : int) : (term77 _48287 _48286) = (term78 _48287 _48286).
Proof. exact (MK_COMB (@lem4106279) (@lem4106277 _48287 _48286)). Qed.
Lemma lem4106281 (_48286 : int) (_48287 : int) : (term79 _48286 _48287) = (term80 _48286 _48287).
Proof. exact (MK_COMB (@lem4106280 _48287 _48286) (@lem4106278 _48286 _48287)). Qed.
Lemma lem4106282 (_48286 : int) (_48287 : int) : (term81 _48286 _48287) = (term79 _48286 _48287).
Proof. exact (@lem17045 (term82 _48287 _48286) (term83 _48286 _48287)). Qed.
Lemma lem4106283 (_48286 : int) (_48287 : int) : (term81 _48286 _48287) = (term80 _48286 _48287).
Proof. exact (TRANS (@lem4106282 _48286 _48287) (@lem4106281 _48286 _48287)). Qed.
Lemma lem4106287 (_48286 : int) (_48287 : int) : (term84 _48286 _48287) = (term83 _48286 _48287).
Proof. exact (@lem16933 (term83 _48286 _48287)). Qed.
Lemma lem4106289 (_48287 : int) (_48286 : int) : (term85 _48287 _48286) = (term85 _48287 _48286).
Proof. exact (eq_refl (term85 _48287 _48286)). Qed.
Lemma lem4106290 (_48286 : int) (_48287 : int) : (term86 _48286 _48287) = (term87 _48286 _48287).
Proof. exact (MK_COMB (@lem4106289 _48287 _48286) (@lem4106287 _48286 _48287)). Qed.
Lemma lem4106291 (_48286 : int) (_48287 : int) : (term88 _48286 _48287) = (term86 _48286 _48287).
Proof. exact (@lem17045 (int_le _48287 _48286) (term76 _48286 _48287)). Qed.
Lemma lem4106292 (_48286 : int) (_48287 : int) : (term88 _48286 _48287) = (term87 _48286 _48287).
Proof. exact (TRANS (@lem4106291 _48286 _48287) (@lem4106290 _48286 _48287)). Qed.
Lemma lem4106293 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4106294 (_48286 : int) (_48287 : int) : (term89 _48286 _48287) = (term90 _48286 _48287).
Proof. exact (MK_COMB (@lem4106293) (@lem4106283 _48286 _48287)). Qed.
Lemma lem4106295 (_48286 : int) (_48287 : int) : (term91 _48286 _48287) = (term92 _48286 _48287).
Proof. exact (MK_COMB (@lem4106294 _48286 _48287) (@lem4106292 _48286 _48287)). Qed.
Lemma lem4106296 (_48286 : int) (_48287 : int) : (term93 _48286 _48287) = (term91 _48286 _48287).
Proof. exact (@lem17160 (term94 _48286 _48287) (term95 _48286 _48287)). Qed.
Lemma lem4106297 (_48286 : int) (_48287 : int) : (term93 _48286 _48287) = (term92 _48286 _48287).
Proof. exact (TRANS (@lem4106296 _48286 _48287) (@lem4106295 _48286 _48287)). Qed.
Lemma lem4106299 (_48287 : int) : (term96 _48287) = (term96 _48287).
Proof. exact (eq_refl (term96 _48287)). Qed.
Lemma lem4106300 (_48286 : int) (_48287 : int) : (term97 _48286 _48287) = (term98 _48286 _48287).
Proof. exact (MK_COMB (@lem4106299 _48287) (@lem4106297 _48286 _48287)). Qed.
Lemma lem4106301 (_48286 : int) (_48287 : int) : (term99 _48286 _48287) = (term97 _48286 _48287).
Proof. exact (@lem17362 (term100 _48287) (term101 _48286 _48287)). Qed.
Lemma lem4106302 (_48286 : int) (_48287 : int) : (term99 _48286 _48287) = (term98 _48286 _48287).
Proof. exact (TRANS (@lem4106301 _48286 _48287) (@lem4106300 _48286 _48287)). Qed.
Lemma lem4106304 (_48286 : int) : (term96 _48286) = (term96 _48286).
Proof. exact (eq_refl (term96 _48286)). Qed.
Lemma lem4106305 (_48286 : int) (_48287 : int) : (term102 _48286 _48287) = (term103 _48286 _48287).
Proof. exact (MK_COMB (@lem4106304 _48286) (@lem4106302 _48286 _48287)). Qed.
Lemma lem4106306 (_48286 : int) (_48287 : int) : (term104 _48286 _48287) = (term102 _48286 _48287).
Proof. exact (@lem17362 (term100 _48286) (term105 _48286 _48287)). Qed.
Lemma lem4106334 (_48286 : int) (_48287 : int) : (term104 _48286 _48287) = (term103 _48286 _48287).
Proof. exact (TRANS (@lem4106306 _48286 _48287) (@lem4106305 _48286 _48287)). Qed.
Lemma lem4106337 (x : int) (y : int) : (int_le x y) = (term106 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4106338 (_48286 : int) : (term100 _48286) = (term107 _48286).
Proof. exact (@lem4106337 term108 _48286). Qed.
Lemma lem4106340 (n : nat) : (term109 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4106341 : term110 = term111.
Proof. exact (@lem4106340 (NUMERAL 0)). Qed.
Lemma lem4106342 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4106343 : term112 = term113.
Proof. exact (MK_COMB (@lem4106342) (@lem4106341)). Qed.
Lemma lem4106344 (_48286 : int) : (real_of_int _48286) = (real_of_int _48286).
Proof. exact (eq_refl (real_of_int _48286)). Qed.
Lemma lem4106345 (_48286 : int) : (term107 _48286) = (term114 _48286).
Proof. exact (MK_COMB (@lem4106343) (@lem4106344 _48286)). Qed.
Lemma lem4106347 (_48286 : int) : (term100 _48286) = (term114 _48286).
Proof. exact (TRANS (@lem4106338 _48286) (@lem4106345 _48286)). Qed.
Lemma lem4106350 (x : int) (y : int) : (int_le x y) = (term106 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4106351 (_48287 : int) : (term100 _48287) = (term107 _48287).
Proof. exact (@lem4106350 term108 _48287). Qed.
Lemma lem4106353 (n : nat) : (term109 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4106354 : term110 = term111.
Proof. exact (@lem4106353 (NUMERAL 0)). Qed.
Lemma lem4106355 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4106356 : term112 = term113.
Proof. exact (MK_COMB (@lem4106355) (@lem4106354)). Qed.
Lemma lem4106357 (_48287 : int) : (real_of_int _48287) = (real_of_int _48287).
Proof. exact (eq_refl (real_of_int _48287)). Qed.
Lemma lem4106358 (_48287 : int) : (term107 _48287) = (term114 _48287).
Proof. exact (MK_COMB (@lem4106356) (@lem4106357 _48287)). Qed.
Lemma lem4106360 (_48287 : int) : (term100 _48287) = (term114 _48287).
Proof. exact (TRANS (@lem4106351 _48287) (@lem4106358 _48287)). Qed.
Lemma lem4106363 (x : int) (y : int) : (int_le x y) = (term106 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4106365 (_48287 : int) (_48286 : int) : (int_le _48287 _48286) = (term106 _48287 _48286).
Proof. exact (@lem4106363 _48287 _48286). Qed.
Lemma lem4106367 (y : int) (x : int) : (term82 x y) = (term83 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem4106368 (_48287 : int) (_48286 : int) : (term76 _48286 _48287) = (term115 _48287 _48286).
Proof. exact (@lem4106367 _48287 (term116 _48286)). Qed.
Lemma lem4106370 (x : int) (y : int) : (int_le x y) = (term106 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4106371 (_48287 : int) (_48286 : int) : (term115 _48287 _48286) = (term117 _48287 _48286).
Proof. exact (@lem4106370 (term116 _48287) (term116 _48286)). Qed.
Lemma lem4106373 (x : int) (y : int) : (term118 x y) = (term119 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem4106374 (_48287 : int) : (term120 _48287) = (term121 _48287).
Proof. exact (@lem4106373 _48287 term122). Qed.
Lemma lem4106376 (n : nat) : (term109 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4106377 : term123 = term124.
Proof. exact (@lem4106376 term61). Qed.
Lemma lem4106378 (_48287 : int) : (term125 _48287) = (term125 _48287).
Proof. exact (eq_refl (term125 _48287)). Qed.
Lemma lem4106379 (_48287 : int) : (term121 _48287) = (term126 _48287).
Proof. exact (MK_COMB (@lem4106378 _48287) (@lem4106377)). Qed.
Lemma lem4106380 (_48287 : int) : (term120 _48287) = (term126 _48287).
Proof. exact (TRANS (@lem4106374 _48287) (@lem4106379 _48287)). Qed.
Lemma lem4106381 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4106382 (_48287 : int) : (term127 _48287) = (term128 _48287).
Proof. exact (MK_COMB (@lem4106381) (@lem4106380 _48287)). Qed.
Lemma lem4106384 (x : int) (y : int) : (term118 x y) = (term119 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem4106385 (_48286 : int) : (term120 _48286) = (term121 _48286).
Proof. exact (@lem4106384 _48286 term122). Qed.
Lemma lem4106387 (n : nat) : (term109 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4106388 : term123 = term124.
Proof. exact (@lem4106387 term61). Qed.
Lemma lem4106389 (_48286 : int) : (term125 _48286) = (term125 _48286).
Proof. exact (eq_refl (term125 _48286)). Qed.
Lemma lem4106390 (_48286 : int) : (term121 _48286) = (term126 _48286).
Proof. exact (MK_COMB (@lem4106389 _48286) (@lem4106388)). Qed.
Lemma lem4106391 (_48286 : int) : (term120 _48286) = (term126 _48286).
Proof. exact (TRANS (@lem4106385 _48286) (@lem4106390 _48286)). Qed.
Lemma lem4106392 (_48287 : int) (_48286 : int) : (term117 _48287 _48286) = (term129 _48287 _48286).
Proof. exact (MK_COMB (@lem4106382 _48287) (@lem4106391 _48286)). Qed.
Lemma lem4106393 (_48287 : int) (_48286 : int) : (term115 _48287 _48286) = (term129 _48287 _48286).
Proof. exact (TRANS (@lem4106371 _48287 _48286) (@lem4106392 _48287 _48286)). Qed.
Lemma lem4106394 (_48287 : int) (_48286 : int) : (term76 _48286 _48287) = (term129 _48287 _48286).
Proof. exact (TRANS (@lem4106368 _48287 _48286) (@lem4106393 _48287 _48286)). Qed.
Lemma lem4106395 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4106396 (_48287 : int) (_48286 : int) : (term78 _48287 _48286) = (term130 _48287 _48286).
Proof. exact (MK_COMB (@lem4106395) (@lem4106365 _48287 _48286)). Qed.
Lemma lem4106397 (_48287 : int) (_48286 : int) : (term80 _48286 _48287) = (term131 _48287 _48286).
Proof. exact (MK_COMB (@lem4106396 _48287 _48286) (@lem4106394 _48287 _48286)). Qed.
Lemma lem4106399 (y : int) (x : int) : (term82 x y) = (term83 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem4106400 (_48286 : int) (_48287 : int) : (term82 _48287 _48286) = (term83 _48286 _48287).
Proof. exact (@lem4106399 _48286 _48287). Qed.
Lemma lem4106402 (x : int) (y : int) : (int_le x y) = (term106 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4106403 (_48286 : int) (_48287 : int) : (term83 _48286 _48287) = (term132 _48286 _48287).
Proof. exact (@lem4106402 (term116 _48286) _48287). Qed.
Lemma lem4106405 (x : int) (y : int) : (term118 x y) = (term119 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem4106406 (_48286 : int) : (term120 _48286) = (term121 _48286).
Proof. exact (@lem4106405 _48286 term122). Qed.
Lemma lem4106408 (n : nat) : (term109 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4106409 : term123 = term124.
Proof. exact (@lem4106408 term61). Qed.
Lemma lem4106410 (_48286 : int) : (term125 _48286) = (term125 _48286).
Proof. exact (eq_refl (term125 _48286)). Qed.
Lemma lem4106411 (_48286 : int) : (term121 _48286) = (term126 _48286).
Proof. exact (MK_COMB (@lem4106410 _48286) (@lem4106409)). Qed.
Lemma lem4106412 (_48286 : int) : (term120 _48286) = (term126 _48286).
Proof. exact (TRANS (@lem4106406 _48286) (@lem4106411 _48286)). Qed.
Lemma lem4106413 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4106414 (_48286 : int) : (term127 _48286) = (term128 _48286).
Proof. exact (MK_COMB (@lem4106413) (@lem4106412 _48286)). Qed.
Lemma lem4106415 (_48287 : int) : (real_of_int _48287) = (real_of_int _48287).
Proof. exact (eq_refl (real_of_int _48287)). Qed.
Lemma lem4106416 (_48286 : int) (_48287 : int) : (term132 _48286 _48287) = (term133 _48286 _48287).
Proof. exact (MK_COMB (@lem4106414 _48286) (@lem4106415 _48287)). Qed.
Lemma lem4106417 (_48286 : int) (_48287 : int) : (term83 _48286 _48287) = (term133 _48286 _48287).
Proof. exact (TRANS (@lem4106403 _48286 _48287) (@lem4106416 _48286 _48287)). Qed.
Lemma lem4106418 (_48286 : int) (_48287 : int) : (term82 _48287 _48286) = (term133 _48286 _48287).
Proof. exact (TRANS (@lem4106400 _48286 _48287) (@lem4106417 _48286 _48287)). Qed.
Lemma lem4106421 (x : int) (y : int) : (int_le x y) = (term106 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4106422 (_48286 : int) (_48287 : int) : (term83 _48286 _48287) = (term132 _48286 _48287).
Proof. exact (@lem4106421 (term116 _48286) _48287). Qed.
Lemma lem4106424 (x : int) (y : int) : (term118 x y) = (term119 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem4106425 (_48286 : int) : (term120 _48286) = (term121 _48286).
Proof. exact (@lem4106424 _48286 term122). Qed.
Lemma lem4106427 (n : nat) : (term109 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4106428 : term123 = term124.
Proof. exact (@lem4106427 term61). Qed.
Lemma lem4106429 (_48286 : int) : (term125 _48286) = (term125 _48286).
Proof. exact (eq_refl (term125 _48286)). Qed.
Lemma lem4106430 (_48286 : int) : (term121 _48286) = (term126 _48286).
Proof. exact (MK_COMB (@lem4106429 _48286) (@lem4106428)). Qed.
Lemma lem4106431 (_48286 : int) : (term120 _48286) = (term126 _48286).
Proof. exact (TRANS (@lem4106425 _48286) (@lem4106430 _48286)). Qed.
Lemma lem4106432 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4106433 (_48286 : int) : (term127 _48286) = (term128 _48286).
Proof. exact (MK_COMB (@lem4106432) (@lem4106431 _48286)). Qed.
Lemma lem4106434 (_48287 : int) : (real_of_int _48287) = (real_of_int _48287).
Proof. exact (eq_refl (real_of_int _48287)). Qed.
Lemma lem4106435 (_48286 : int) (_48287 : int) : (term132 _48286 _48287) = (term133 _48286 _48287).
Proof. exact (MK_COMB (@lem4106433 _48286) (@lem4106434 _48287)). Qed.
Lemma lem4106437 (_48286 : int) (_48287 : int) : (term83 _48286 _48287) = (term133 _48286 _48287).
Proof. exact (TRANS (@lem4106422 _48286 _48287) (@lem4106435 _48286 _48287)). Qed.
Lemma lem4106438 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4106439 (_48286 : int) (_48287 : int) : (term85 _48287 _48286) = (term134 _48286 _48287).
Proof. exact (MK_COMB (@lem4106438) (@lem4106418 _48286 _48287)). Qed.
Lemma lem4106440 (_48286 : int) (_48287 : int) : (term87 _48286 _48287) = (term135 _48286 _48287).
Proof. exact (MK_COMB (@lem4106439 _48286 _48287) (@lem4106437 _48286 _48287)). Qed.
Lemma lem4106441 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4106442 (_48287 : int) (_48286 : int) : (term90 _48286 _48287) = (term136 _48287 _48286).
Proof. exact (MK_COMB (@lem4106441) (@lem4106397 _48287 _48286)). Qed.
Lemma lem4106443 (_48286 : int) (_48287 : int) : (term92 _48286 _48287) = (term137 _48286 _48287).
Proof. exact (MK_COMB (@lem4106442 _48287 _48286) (@lem4106440 _48286 _48287)). Qed.
Lemma lem4106444 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4106445 (_48287 : int) : (term96 _48287) = (term138 _48287).
Proof. exact (MK_COMB (@lem4106444) (@lem4106360 _48287)). Qed.
Lemma lem4106446 (_48286 : int) (_48287 : int) : (term98 _48286 _48287) = (term139 _48286 _48287).
Proof. exact (MK_COMB (@lem4106445 _48287) (@lem4106443 _48286 _48287)). Qed.
Lemma lem4106447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4106448 (_48286 : int) : (term96 _48286) = (term138 _48286).
Proof. exact (MK_COMB (@lem4106447) (@lem4106347 _48286)). Qed.
Lemma lem4106449 (_48286 : int) (_48287 : int) : (term103 _48286 _48287) = (term140 _48286 _48287).
Proof. exact (MK_COMB (@lem4106448 _48286) (@lem4106446 _48286 _48287)). Qed.
Lemma lem4106450 (_48286 : int) (_48287 : int) : (term104 _48286 _48287) = (term140 _48286 _48287).
Proof. exact (TRANS (@lem4106334 _48286 _48287) (@lem4106449 _48286 _48287)). Qed.
Lemma lem4106454 (t : Prop) : (term141 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4106455 (_48286 : int) (_48287 : int) : (term142 _48286 _48287) = (term140 _48286 _48287).
Proof. exact (@lem4106454 (term140 _48286 _48287)). Qed.
Lemma lem4106465 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem16485 t)). Qed.
Lemma lem4106466 (_48286 : int) (_48287 : int) : (term135 _48286 _48287) = (term133 _48286 _48287).
Proof. exact (@lem4106465 (term133 _48286 _48287)). Qed.
Lemma lem4106467 (_48287 : int) (_48286 : int) : (term136 _48287 _48286) = (term136 _48287 _48286).
Proof. exact (eq_refl (term136 _48287 _48286)). Qed.
Lemma lem4106468 (_48286 : int) (_48287 : int) : (term137 _48286 _48287) = (term143 _48286 _48287).
Proof. exact (MK_COMB (@lem4106467 _48287 _48286) (@lem4106466 _48286 _48287)). Qed.
Lemma lem4106471 (_48287 : int) : (term138 _48287) = (term138 _48287).
Proof. exact (eq_refl (term138 _48287)). Qed.
Lemma lem4106472 (_48286 : int) (_48287 : int) : (term139 _48286 _48287) = (term144 _48286 _48287).
Proof. exact (MK_COMB (@lem4106471 _48287) (@lem4106468 _48286 _48287)). Qed.
Lemma lem4106475 (_48286 : int) : (term138 _48286) = (term138 _48286).
Proof. exact (eq_refl (term138 _48286)). Qed.
Lemma lem4106476 (_48286 : int) (_48287 : int) : (term140 _48286 _48287) = (term145 _48286 _48287).
Proof. exact (MK_COMB (@lem4106475 _48286) (@lem4106472 _48286 _48287)). Qed.
Lemma lem4106516 (_48286 : int) (_48287 : int) : (term142 _48286 _48287) = (term145 _48286 _48287).
Proof. exact (TRANS (@lem4106455 _48286 _48287) (@lem4106476 _48286 _48287)). Qed.
Lemma lem4106517 (_48286 : int) : (term114 _48286) = (term146 _48286).
Proof. exact (@lem1988287 (real_of_int _48286) term111). Qed.
Lemma lem4106523 (_48286 : int) : (term147 _48286) = (term148 _48286).
Proof. exact (@lem1982792 (real_of_int _48286) term111). Qed.
Lemma lem4106525 (x : nat) : (real_of_num x) = (term149 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4106526 : term111 = term150.
Proof. exact (@lem4106525 (NUMERAL 0)). Qed.
Lemma lem4106528 (x : nat) : (term151 x) = (term152 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4106529 : term153 = term154.
Proof. exact (@lem4106528 term61). Qed.
Lemma lem4106530 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4106531 : term155 = term156.
Proof. exact (MK_COMB (@lem4106530) (@lem4106529)). Qed.
Lemma lem4106532 : term157 = term158.
Proof. exact (MK_COMB (@lem4106531) (@lem4106526)). Qed.
Lemma lem4106533 : term158 = term159.
Proof. exact (@lem1981613 term153 term111 term124 term124). Qed.
Lemma lem4106535 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4106536 : term162 = term163.
Proof. exact (@lem4106535 term61 term61). Qed.
Lemma lem4106537 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4106538 : term165 = term61.
Proof. exact (EQ_MP (@lem4106537) (@lem940073)). Qed.
Lemma lem4106539 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4106540 : term163 = term124.
Proof. exact (MK_COMB (@lem4106539) (@lem4106538)). Qed.
Lemma lem4106541 : term162 = term124.
Proof. exact (TRANS (@lem4106536) (@lem4106540)). Qed.
Lemma lem4106543 (x : nat) : (term166 x) = term111.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem4106544 : term157 = term111.
Proof. exact (@lem4106543 term61). Qed.
Lemma lem4106545 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4106546 : term167 = term168.
Proof. exact (MK_COMB (@lem4106545) (@lem4106544)). Qed.
Lemma lem4106547 : term159 = term150.
Proof. exact (MK_COMB (@lem4106546) (@lem4106541)). Qed.
Lemma lem4106548 : term158 = term150.
Proof. exact (TRANS (@lem4106533) (@lem4106547)). Qed.
Lemma lem4106549 : term157 = term150.
Proof. exact (TRANS (@lem4106532) (@lem4106548)). Qed.
Lemma lem4106551 (x : real) : (term169 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4106552 : term150 = term111.
Proof. exact (@lem4106551 term111). Qed.
Lemma lem4106553 : term157 = term111.
Proof. exact (TRANS (@lem4106549) (@lem4106552)). Qed.
Lemma lem4106554 (_48286 : int) : (term125 _48286) = (term125 _48286).
Proof. exact (eq_refl (term125 _48286)). Qed.
Lemma lem4106555 (_48286 : int) : (term148 _48286) = (term170 _48286).
Proof. exact (MK_COMB (@lem4106554 _48286) (@lem4106553)). Qed.
Lemma lem4106556 (_48286 : int) : (term170 _48286) = (real_of_int _48286).
Proof. exact (@lem1982723 (real_of_int _48286)). Qed.
Lemma lem4106557 (_48286 : int) : (term148 _48286) = (real_of_int _48286).
Proof. exact (TRANS (@lem4106555 _48286) (@lem4106556 _48286)). Qed.
Lemma lem4106559 (_48286 : int) : (term147 _48286) = (real_of_int _48286).
Proof. exact (TRANS (@lem4106523 _48286) (@lem4106557 _48286)). Qed.
Lemma lem4106560 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4106561 (_48286 : int) : (term171 _48286) = (term172 _48286).
Proof. exact (MK_COMB (@lem4106560) (@lem4106559 _48286)). Qed.
Lemma lem4106562 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4106563 (_48286 : int) : (term146 _48286) = (term173 _48286).
Proof. exact (MK_COMB (@lem4106561 _48286) (@lem4106562)). Qed.
Lemma lem4106564 (_48286 : int) : (term114 _48286) = (term173 _48286).
Proof. exact (TRANS (@lem4106517 _48286) (@lem4106563 _48286)). Qed.
Lemma lem4106565 (_48287 : int) : (term114 _48287) = (term146 _48287).
Proof. exact (@lem1988287 (real_of_int _48287) term111). Qed.
Lemma lem4106571 (_48287 : int) : (term147 _48287) = (term148 _48287).
Proof. exact (@lem1982792 (real_of_int _48287) term111). Qed.
Lemma lem4106573 (x : nat) : (real_of_num x) = (term149 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4106574 : term111 = term150.
Proof. exact (@lem4106573 (NUMERAL 0)). Qed.
Lemma lem4106576 (x : nat) : (term151 x) = (term152 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4106577 : term153 = term154.
Proof. exact (@lem4106576 term61). Qed.
Lemma lem4106578 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4106579 : term155 = term156.
Proof. exact (MK_COMB (@lem4106578) (@lem4106577)). Qed.
Lemma lem4106580 : term157 = term158.
Proof. exact (MK_COMB (@lem4106579) (@lem4106574)). Qed.
Lemma lem4106581 : term158 = term159.
Proof. exact (@lem1981613 term153 term111 term124 term124). Qed.
Lemma lem4106583 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4106584 : term162 = term163.
Proof. exact (@lem4106583 term61 term61). Qed.
Lemma lem4106585 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4106586 : term165 = term61.
Proof. exact (EQ_MP (@lem4106585) (@lem940073)). Qed.
Lemma lem4106587 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4106588 : term163 = term124.
Proof. exact (MK_COMB (@lem4106587) (@lem4106586)). Qed.
Lemma lem4106589 : term162 = term124.
Proof. exact (TRANS (@lem4106584) (@lem4106588)). Qed.
Lemma lem4106591 (x : nat) : (term166 x) = term111.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem4106592 : term157 = term111.
Proof. exact (@lem4106591 term61). Qed.
Lemma lem4106593 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4106594 : term167 = term168.
Proof. exact (MK_COMB (@lem4106593) (@lem4106592)). Qed.
Lemma lem4106595 : term159 = term150.
Proof. exact (MK_COMB (@lem4106594) (@lem4106589)). Qed.
Lemma lem4106596 : term158 = term150.
Proof. exact (TRANS (@lem4106581) (@lem4106595)). Qed.
Lemma lem4106597 : term157 = term150.
Proof. exact (TRANS (@lem4106580) (@lem4106596)). Qed.
Lemma lem4106599 (x : real) : (term169 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4106600 : term150 = term111.
Proof. exact (@lem4106599 term111). Qed.
Lemma lem4106601 : term157 = term111.
Proof. exact (TRANS (@lem4106597) (@lem4106600)). Qed.
Lemma lem4106602 (_48287 : int) : (term125 _48287) = (term125 _48287).
Proof. exact (eq_refl (term125 _48287)). Qed.
Lemma lem4106603 (_48287 : int) : (term148 _48287) = (term170 _48287).
Proof. exact (MK_COMB (@lem4106602 _48287) (@lem4106601)). Qed.
Lemma lem4106604 (_48287 : int) : (term170 _48287) = (real_of_int _48287).
Proof. exact (@lem1982723 (real_of_int _48287)). Qed.
Lemma lem4106605 (_48287 : int) : (term148 _48287) = (real_of_int _48287).
Proof. exact (TRANS (@lem4106603 _48287) (@lem4106604 _48287)). Qed.
Lemma lem4106607 (_48287 : int) : (term147 _48287) = (real_of_int _48287).
Proof. exact (TRANS (@lem4106571 _48287) (@lem4106605 _48287)). Qed.
Lemma lem4106608 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4106609 (_48287 : int) : (term171 _48287) = (term172 _48287).
Proof. exact (MK_COMB (@lem4106608) (@lem4106607 _48287)). Qed.
Lemma lem4106610 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4106611 (_48287 : int) : (term146 _48287) = (term173 _48287).
Proof. exact (MK_COMB (@lem4106609 _48287) (@lem4106610)). Qed.
Lemma lem4106612 (_48287 : int) : (term114 _48287) = (term173 _48287).
Proof. exact (TRANS (@lem4106565 _48287) (@lem4106611 _48287)). Qed.
Lemma lem4106613 (_48286 : int) (_48287 : int) : (term106 _48287 _48286) = (term174 _48286 _48287).
Proof. exact (@lem1988287 (real_of_int _48286) (real_of_int _48287)). Qed.
Lemma lem4106626 (_48286 : int) (_48287 : int) : (term175 _48286 _48287) = (term176 _48286 _48287).
Proof. exact (@lem1982792 (real_of_int _48286) (real_of_int _48287)). Qed.
Lemma lem4106627 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4106628 (_48286 : int) (_48287 : int) : (term177 _48286 _48287) = (term178 _48286 _48287).
Proof. exact (MK_COMB (@lem4106627) (@lem4106626 _48286 _48287)). Qed.
Lemma lem4106629 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4106630 (_48286 : int) (_48287 : int) : (term174 _48286 _48287) = (term179 _48286 _48287).
Proof. exact (MK_COMB (@lem4106628 _48286 _48287) (@lem4106629)). Qed.
Lemma lem4106631 (_48286 : int) (_48287 : int) : (term106 _48287 _48286) = (term179 _48286 _48287).
Proof. exact (TRANS (@lem4106613 _48286 _48287) (@lem4106630 _48286 _48287)). Qed.
Lemma lem4106632 (_48286 : int) (_48287 : int) : (term129 _48287 _48286) = (term180 _48286 _48287).
Proof. exact (@lem1988287 (term126 _48286) (term126 _48287)). Qed.
Lemma lem4106650 (_48286 : int) (_48287 : int) : (term181 _48286 _48287) = (term182 _48286 _48287).
Proof. exact (@lem1982792 (term126 _48286) (term126 _48287)). Qed.
Lemma lem4106651 (_48287 : int) : (term183 _48287) = (term184 _48287).
Proof. exact (@lem1982781 (real_of_int _48287) term153 term124). Qed.
Lemma lem4106653 (x : nat) : (real_of_num x) = (term149 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4106654 : term124 = term185.
Proof. exact (@lem4106653 term61). Qed.
Lemma lem4106656 (x : nat) : (term151 x) = (term152 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4106657 : term153 = term154.
Proof. exact (@lem4106656 term61). Qed.
Lemma lem4106658 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4106659 : term155 = term156.
Proof. exact (MK_COMB (@lem4106658) (@lem4106657)). Qed.
Lemma lem4106660 : term186 = term187.
Proof. exact (MK_COMB (@lem4106659) (@lem4106654)). Qed.
Lemma lem4106661 : term187 = term188.
Proof. exact (@lem1981613 term153 term124 term124 term124). Qed.
Lemma lem4106663 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4106664 : term162 = term163.
Proof. exact (@lem4106663 term61 term61). Qed.
Lemma lem4106665 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4106666 : term165 = term61.
Proof. exact (EQ_MP (@lem4106665) (@lem940073)). Qed.
Lemma lem4106667 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4106668 : term163 = term124.
Proof. exact (MK_COMB (@lem4106667) (@lem4106666)). Qed.
Lemma lem4106669 : term162 = term124.
Proof. exact (TRANS (@lem4106664) (@lem4106668)). Qed.
Lemma lem4106671 (m : nat) (n : nat) : (term189 m n) = (term190 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4106672 : term186 = term191.
Proof. exact (@lem4106671 term61 term61). Qed.
Lemma lem4106673 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4106674 : term165 = term61.
Proof. exact (EQ_MP (@lem4106673) (@lem940073)). Qed.
Lemma lem4106675 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4106676 : term163 = term124.
Proof. exact (MK_COMB (@lem4106675) (@lem4106674)). Qed.
Lemma lem4106677 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4106678 : term191 = term153.
Proof. exact (MK_COMB (@lem4106677) (@lem4106676)). Qed.
Lemma lem4106679 : term186 = term153.
Proof. exact (TRANS (@lem4106672) (@lem4106678)). Qed.
Lemma lem4106680 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4106681 : term192 = term193.
Proof. exact (MK_COMB (@lem4106680) (@lem4106679)). Qed.
Lemma lem4106682 : term188 = term154.
Proof. exact (MK_COMB (@lem4106681) (@lem4106669)). Qed.
Lemma lem4106683 : term187 = term154.
Proof. exact (TRANS (@lem4106661) (@lem4106682)). Qed.
Lemma lem4106684 : term186 = term154.
Proof. exact (TRANS (@lem4106660) (@lem4106683)). Qed.
Lemma lem4106686 (x : real) : (term169 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4106687 : term154 = term153.
Proof. exact (@lem4106686 term153). Qed.
Lemma lem4106688 : term186 = term153.
Proof. exact (TRANS (@lem4106684) (@lem4106687)). Qed.
Lemma lem4106691 (_48287 : int) : (term194 _48287) = (term194 _48287).
Proof. exact (eq_refl (term194 _48287)). Qed.
Lemma lem4106692 (_48287 : int) : (term184 _48287) = (term195 _48287).
Proof. exact (MK_COMB (@lem4106691 _48287) (@lem4106688)). Qed.
Lemma lem4106693 (_48287 : int) : (term183 _48287) = (term195 _48287).
Proof. exact (TRANS (@lem4106651 _48287) (@lem4106692 _48287)). Qed.
Lemma lem4106694 (_48286 : int) : (term196 _48286) = (term196 _48286).
Proof. exact (eq_refl (term196 _48286)). Qed.
Lemma lem4106695 (_48286 : int) (_48287 : int) : (term182 _48286 _48287) = (term197 _48286 _48287).
Proof. exact (MK_COMB (@lem4106694 _48286) (@lem4106693 _48287)). Qed.
Lemma lem4106696 (_48286 : int) (_48287 : int) : (term197 _48286 _48287) = (term198 _48286 _48287).
Proof. exact (@lem1982755 (real_of_int _48286) term124 (term195 _48287)). Qed.
Lemma lem4106697 (_48287 : int) : (term199 _48287) = (term200 _48287).
Proof. exact (@lem1982757 (term201 _48287) term124 term153). Qed.
Lemma lem4106699 (x : nat) : (term151 x) = (term152 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4106700 : term153 = term154.
Proof. exact (@lem4106699 term61). Qed.
Lemma lem4106702 (x : nat) : (real_of_num x) = (term149 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4106703 : term124 = term185.
Proof. exact (@lem4106702 term61). Qed.
Lemma lem4106704 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4106705 : term202 = term203.
Proof. exact (MK_COMB (@lem4106704) (@lem4106703)). Qed.
Lemma lem4106706 : term204 = term205.
Proof. exact (MK_COMB (@lem4106705) (@lem4106700)). Qed.
Lemma lem4106707 : term206.
Proof. exact (@lem1981473 term124 term124 term153 term124 term111 term124). Qed.
Lemma lem4106709 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4106710 : term208 = term209.
Proof. exact (@lem4106709 (NUMERAL 0) term61). Qed.
Lemma lem4106711 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4106712 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4106713 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4106712 h1) (fun h1 : term209 = True => @lem4106711)). Qed.
Lemma lem4106714 : term209 = True.
Proof. exact (EQ_MP (@lem4106713) (@lem4106711)). Qed.
Lemma lem4106715 : term208 = True.
Proof. exact (TRANS (@lem4106710) (@lem4106714)). Qed.
Lemma lem4106716 : True = term208.
Proof. exact (SYM (@lem4106715)). Qed.
Lemma lem4106717 : term208.
Proof. exact (EQ_MP (@lem4106716) (@lem0)). Qed.
Lemma lem4106718 : term211.
Proof. exact (@lem4106707 (@lem4106717)). Qed.
Lemma lem4106720 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4106721 : term208 = term209.
Proof. exact (@lem4106720 (NUMERAL 0) term61). Qed.
Lemma lem4106722 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4106723 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4106724 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4106723 h1) (fun h1 : term209 = True => @lem4106722)). Qed.
Lemma lem4106725 : term209 = True.
Proof. exact (EQ_MP (@lem4106724) (@lem4106722)). Qed.
Lemma lem4106726 : term208 = True.
Proof. exact (TRANS (@lem4106721) (@lem4106725)). Qed.
Lemma lem4106727 : True = term208.
Proof. exact (SYM (@lem4106726)). Qed.
Lemma lem4106728 : term208.
Proof. exact (EQ_MP (@lem4106727) (@lem0)). Qed.
Lemma lem4106729 : term212.
Proof. exact (@lem4106718 (@lem4106728)). Qed.
Lemma lem4106731 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4106732 : term208 = term209.
Proof. exact (@lem4106731 (NUMERAL 0) term61). Qed.
Lemma lem4106733 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4106734 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4106735 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4106734 h1) (fun h1 : term209 = True => @lem4106733)). Qed.
Lemma lem4106736 : term209 = True.
Proof. exact (EQ_MP (@lem4106735) (@lem4106733)). Qed.
Lemma lem4106737 : term208 = True.
Proof. exact (TRANS (@lem4106732) (@lem4106736)). Qed.
Lemma lem4106738 : True = term208.
Proof. exact (SYM (@lem4106737)). Qed.
Lemma lem4106739 : term208.
Proof. exact (EQ_MP (@lem4106738) (@lem0)). Qed.
Lemma lem4106740 : term213.
Proof. exact (@lem4106729 (@lem4106739)). Qed.
Lemma lem4106742 (m : nat) (n : nat) : (term189 m n) = (term190 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4106743 : term186 = term191.
Proof. exact (@lem4106742 term61 term61). Qed.
Lemma lem4106744 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4106745 : term165 = term61.
Proof. exact (EQ_MP (@lem4106744) (@lem940073)). Qed.
Lemma lem4106746 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4106747 : term163 = term124.
Proof. exact (MK_COMB (@lem4106746) (@lem4106745)). Qed.
Lemma lem4106748 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4106749 : term191 = term153.
Proof. exact (MK_COMB (@lem4106748) (@lem4106747)). Qed.
Lemma lem4106750 : term186 = term153.
Proof. exact (TRANS (@lem4106743) (@lem4106749)). Qed.
Lemma lem4106752 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4106753 : term162 = term163.
Proof. exact (@lem4106752 term61 term61). Qed.
Lemma lem4106754 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4106755 : term165 = term61.
Proof. exact (EQ_MP (@lem4106754) (@lem940073)). Qed.
Lemma lem4106756 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4106757 : term163 = term124.
Proof. exact (MK_COMB (@lem4106756) (@lem4106755)). Qed.
Lemma lem4106758 : term162 = term124.
Proof. exact (TRANS (@lem4106753) (@lem4106757)). Qed.
Lemma lem4106759 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4106760 : term214 = term202.
Proof. exact (MK_COMB (@lem4106759) (@lem4106758)). Qed.
Lemma lem4106761 : term215 = term204.
Proof. exact (MK_COMB (@lem4106760) (@lem4106750)). Qed.
Lemma lem4106763 (m : nat) : (term216 m) = term111.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem4106764 : term204 = term111.
Proof. exact (@lem4106763 term61). Qed.
Lemma lem4106765 : term215 = term111.
Proof. exact (TRANS (@lem4106761) (@lem4106764)). Qed.
Lemma lem4106766 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4106767 : term217 = term218.
Proof. exact (MK_COMB (@lem4106766) (@lem4106765)). Qed.
Lemma lem4106768 : term124 = term124.
Proof. exact (eq_refl term124). Qed.
Lemma lem4106769 : term219 = term220.
Proof. exact (MK_COMB (@lem4106767) (@lem4106768)). Qed.
Lemma lem4106771 (x : nat) : (term221 x) = term111.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4106772 : term220 = term111.
Proof. exact (@lem4106771 term61). Qed.
Lemma lem4106773 : term219 = term111.
Proof. exact (TRANS (@lem4106769) (@lem4106772)). Qed.
Lemma lem4106775 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4106776 : term162 = term163.
Proof. exact (@lem4106775 term61 term61). Qed.
Lemma lem4106777 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4106778 : term165 = term61.
Proof. exact (EQ_MP (@lem4106777) (@lem940073)). Qed.
Lemma lem4106779 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4106780 : term163 = term124.
Proof. exact (MK_COMB (@lem4106779) (@lem4106778)). Qed.
Lemma lem4106781 : term162 = term124.
Proof. exact (TRANS (@lem4106776) (@lem4106780)). Qed.
Lemma lem4106782 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem4106783 : term222 = term220.
Proof. exact (MK_COMB (@lem4106782) (@lem4106781)). Qed.
Lemma lem4106785 (x : nat) : (term221 x) = term111.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4106786 : term220 = term111.
Proof. exact (@lem4106785 term61). Qed.
Lemma lem4106787 : term222 = term111.
Proof. exact (TRANS (@lem4106783) (@lem4106786)). Qed.
Lemma lem4106788 : term111 = term222.
Proof. exact (SYM (@lem4106787)). Qed.
Lemma lem4106789 : term219 = term222.
Proof. exact (TRANS (@lem4106773) (@lem4106788)). Qed.
Lemma lem4106790 : term205 = term150.
Proof. exact (@lem4106740 (@lem4106789)). Qed.
Lemma lem4106791 : term204 = term150.
Proof. exact (TRANS (@lem4106706) (@lem4106790)). Qed.
Lemma lem4106793 (x : real) : (term169 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4106794 : term150 = term111.
Proof. exact (@lem4106793 term111). Qed.
Lemma lem4106795 : term204 = term111.
Proof. exact (TRANS (@lem4106791) (@lem4106794)). Qed.
Lemma lem4106796 (_48287 : int) : (term194 _48287) = (term194 _48287).
Proof. exact (eq_refl (term194 _48287)). Qed.
Lemma lem4106797 (_48287 : int) : (term200 _48287) = (term223 _48287).
Proof. exact (MK_COMB (@lem4106796 _48287) (@lem4106795)). Qed.
Lemma lem4106798 (_48287 : int) : (term199 _48287) = (term223 _48287).
Proof. exact (TRANS (@lem4106697 _48287) (@lem4106797 _48287)). Qed.
Lemma lem4106799 (_48287 : int) : (term223 _48287) = (term201 _48287).
Proof. exact (@lem1982723 (term201 _48287)). Qed.
Lemma lem4106800 (_48287 : int) : (term199 _48287) = (term201 _48287).
Proof. exact (TRANS (@lem4106798 _48287) (@lem4106799 _48287)). Qed.
Lemma lem4106801 (_48286 : int) : (term125 _48286) = (term125 _48286).
Proof. exact (eq_refl (term125 _48286)). Qed.
Lemma lem4106802 (_48286 : int) (_48287 : int) : (term198 _48286 _48287) = (term176 _48286 _48287).
Proof. exact (MK_COMB (@lem4106801 _48286) (@lem4106800 _48287)). Qed.
Lemma lem4106803 (_48286 : int) (_48287 : int) : (term197 _48286 _48287) = (term176 _48286 _48287).
Proof. exact (TRANS (@lem4106696 _48286 _48287) (@lem4106802 _48286 _48287)). Qed.
Lemma lem4106804 (_48286 : int) (_48287 : int) : (term182 _48286 _48287) = (term176 _48286 _48287).
Proof. exact (TRANS (@lem4106695 _48286 _48287) (@lem4106803 _48286 _48287)). Qed.
Lemma lem4106806 (_48286 : int) (_48287 : int) : (term181 _48286 _48287) = (term176 _48286 _48287).
Proof. exact (TRANS (@lem4106650 _48286 _48287) (@lem4106804 _48286 _48287)). Qed.
Lemma lem4106807 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4106808 (_48286 : int) (_48287 : int) : (term224 _48286 _48287) = (term178 _48286 _48287).
Proof. exact (MK_COMB (@lem4106807) (@lem4106806 _48286 _48287)). Qed.
Lemma lem4106809 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4106810 (_48286 : int) (_48287 : int) : (term180 _48286 _48287) = (term179 _48286 _48287).
Proof. exact (MK_COMB (@lem4106808 _48286 _48287) (@lem4106809)). Qed.
Lemma lem4106811 (_48286 : int) (_48287 : int) : (term129 _48287 _48286) = (term179 _48286 _48287).
Proof. exact (TRANS (@lem4106632 _48286 _48287) (@lem4106810 _48286 _48287)). Qed.
Lemma lem4106812 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4106813 (_48286 : int) (_48287 : int) : (term130 _48287 _48286) = (term225 _48286 _48287).
Proof. exact (MK_COMB (@lem4106812) (@lem4106631 _48286 _48287)). Qed.
Lemma lem4106814 (_48286 : int) (_48287 : int) : (term131 _48287 _48286) = (term226 _48286 _48287).
Proof. exact (MK_COMB (@lem4106813 _48286 _48287) (@lem4106811 _48286 _48287)). Qed.
Lemma lem4106815 (_48287 : int) (_48286 : int) : (term133 _48286 _48287) = (term227 _48287 _48286).
Proof. exact (@lem1988287 (real_of_int _48287) (term126 _48286)). Qed.
Lemma lem4106827 (_48287 : int) (_48286 : int) : (term228 _48287 _48286) = (term229 _48287 _48286).
Proof. exact (@lem1982792 (real_of_int _48287) (term126 _48286)). Qed.
Lemma lem4106828 (_48286 : int) : (term183 _48286) = (term184 _48286).
Proof. exact (@lem1982781 (real_of_int _48286) term153 term124). Qed.
Lemma lem4106830 (x : nat) : (real_of_num x) = (term149 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4106831 : term124 = term185.
Proof. exact (@lem4106830 term61). Qed.
Lemma lem4106833 (x : nat) : (term151 x) = (term152 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4106834 : term153 = term154.
Proof. exact (@lem4106833 term61). Qed.
Lemma lem4106835 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4106836 : term155 = term156.
Proof. exact (MK_COMB (@lem4106835) (@lem4106834)). Qed.
Lemma lem4106837 : term186 = term187.
Proof. exact (MK_COMB (@lem4106836) (@lem4106831)). Qed.
Lemma lem4106838 : term187 = term188.
Proof. exact (@lem1981613 term153 term124 term124 term124). Qed.
Lemma lem4106840 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4106841 : term162 = term163.
Proof. exact (@lem4106840 term61 term61). Qed.
Lemma lem4106842 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4106843 : term165 = term61.
Proof. exact (EQ_MP (@lem4106842) (@lem940073)). Qed.
Lemma lem4106844 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4106845 : term163 = term124.
Proof. exact (MK_COMB (@lem4106844) (@lem4106843)). Qed.
Lemma lem4106846 : term162 = term124.
Proof. exact (TRANS (@lem4106841) (@lem4106845)). Qed.
Lemma lem4106848 (m : nat) (n : nat) : (term189 m n) = (term190 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4106849 : term186 = term191.
Proof. exact (@lem4106848 term61 term61). Qed.
Lemma lem4106850 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4106851 : term165 = term61.
Proof. exact (EQ_MP (@lem4106850) (@lem940073)). Qed.
Lemma lem4106852 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4106853 : term163 = term124.
Proof. exact (MK_COMB (@lem4106852) (@lem4106851)). Qed.
Lemma lem4106854 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4106855 : term191 = term153.
Proof. exact (MK_COMB (@lem4106854) (@lem4106853)). Qed.
Lemma lem4106856 : term186 = term153.
Proof. exact (TRANS (@lem4106849) (@lem4106855)). Qed.
Lemma lem4106857 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4106858 : term192 = term193.
Proof. exact (MK_COMB (@lem4106857) (@lem4106856)). Qed.
Lemma lem4106859 : term188 = term154.
Proof. exact (MK_COMB (@lem4106858) (@lem4106846)). Qed.
Lemma lem4106860 : term187 = term154.
Proof. exact (TRANS (@lem4106838) (@lem4106859)). Qed.
Lemma lem4106861 : term186 = term154.
Proof. exact (TRANS (@lem4106837) (@lem4106860)). Qed.
Lemma lem4106863 (x : real) : (term169 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4106864 : term154 = term153.
Proof. exact (@lem4106863 term153). Qed.
Lemma lem4106865 : term186 = term153.
Proof. exact (TRANS (@lem4106861) (@lem4106864)). Qed.
Lemma lem4106868 (_48286 : int) : (term194 _48286) = (term194 _48286).
Proof. exact (eq_refl (term194 _48286)). Qed.
Lemma lem4106869 (_48286 : int) : (term184 _48286) = (term195 _48286).
Proof. exact (MK_COMB (@lem4106868 _48286) (@lem4106865)). Qed.
Lemma lem4106870 (_48286 : int) : (term183 _48286) = (term195 _48286).
Proof. exact (TRANS (@lem4106828 _48286) (@lem4106869 _48286)). Qed.
Lemma lem4106871 (_48287 : int) : (term125 _48287) = (term125 _48287).
Proof. exact (eq_refl (term125 _48287)). Qed.
Lemma lem4106872 (_48287 : int) (_48286 : int) : (term229 _48287 _48286) = (term230 _48287 _48286).
Proof. exact (MK_COMB (@lem4106871 _48287) (@lem4106870 _48286)). Qed.
Lemma lem4106877 (_48286 : int) (_48287 : int) : (term230 _48287 _48286) = (term231 _48286 _48287).
Proof. exact (@lem1982757 (term201 _48286) (real_of_int _48287) term153). Qed.
Lemma lem4106878 (_48286 : int) (_48287 : int) : (term229 _48287 _48286) = (term231 _48286 _48287).
Proof. exact (TRANS (@lem4106872 _48287 _48286) (@lem4106877 _48286 _48287)). Qed.
Lemma lem4106880 (_48286 : int) (_48287 : int) : (term228 _48287 _48286) = (term231 _48286 _48287).
Proof. exact (TRANS (@lem4106827 _48287 _48286) (@lem4106878 _48286 _48287)). Qed.
Lemma lem4106881 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4106882 (_48286 : int) (_48287 : int) : (term232 _48287 _48286) = (term233 _48286 _48287).
Proof. exact (MK_COMB (@lem4106881) (@lem4106880 _48286 _48287)). Qed.
Lemma lem4106883 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4106884 (_48286 : int) (_48287 : int) : (term227 _48287 _48286) = (term234 _48286 _48287).
Proof. exact (MK_COMB (@lem4106882 _48286 _48287) (@lem4106883)). Qed.
Lemma lem4106885 (_48286 : int) (_48287 : int) : (term133 _48286 _48287) = (term234 _48286 _48287).
Proof. exact (TRANS (@lem4106815 _48287 _48286) (@lem4106884 _48286 _48287)). Qed.
Lemma lem4106886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4106887 (_48286 : int) (_48287 : int) : (term136 _48287 _48286) = (term235 _48286 _48287).
Proof. exact (MK_COMB (@lem4106886) (@lem4106814 _48286 _48287)). Qed.
Lemma lem4106888 (_48286 : int) (_48287 : int) : (term143 _48286 _48287) = (term236 _48286 _48287).
Proof. exact (MK_COMB (@lem4106887 _48286 _48287) (@lem4106885 _48286 _48287)). Qed.
Lemma lem4106889 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4106890 (_48287 : int) : (term138 _48287) = (term237 _48287).
Proof. exact (MK_COMB (@lem4106889) (@lem4106612 _48287)). Qed.
Lemma lem4106891 (_48286 : int) (_48287 : int) : (term144 _48286 _48287) = (term238 _48286 _48287).
Proof. exact (MK_COMB (@lem4106890 _48287) (@lem4106888 _48286 _48287)). Qed.
Lemma lem4106892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4106893 (_48286 : int) : (term138 _48286) = (term237 _48286).
Proof. exact (MK_COMB (@lem4106892) (@lem4106564 _48286)). Qed.
Lemma lem4106894 (_48286 : int) (_48287 : int) : (term145 _48286 _48287) = (term239 _48286 _48287).
Proof. exact (MK_COMB (@lem4106893 _48286) (@lem4106891 _48286 _48287)). Qed.
Lemma lem4106901 (_48286 : int) (_48287 : int) : (term142 _48286 _48287) = (term239 _48286 _48287).
Proof. exact (TRANS (@lem4106516 _48286 _48287) (@lem4106894 _48286 _48287)). Qed.
Lemma lem4106918 (_48286 : int) (_48287 : int) : (term236 _48286 _48287) = (term240 _48286 _48287).
Proof. exact (@lem19367 (term179 _48286 _48287) (term179 _48286 _48287) (term234 _48286 _48287)). Qed.
Lemma lem4106921 (_48287 : int) : (term237 _48287) = (term237 _48287).
Proof. exact (eq_refl (term237 _48287)). Qed.
Lemma lem4106922 (_48286 : int) (_48287 : int) : (term238 _48286 _48287) = (term241 _48286 _48287).
Proof. exact (MK_COMB (@lem4106921 _48287) (@lem4106918 _48286 _48287)). Qed.
Lemma lem4106929 (_48286 : int) (_48287 : int) : (term241 _48286 _48287) = (term242 _48286 _48287).
Proof. exact (@lem19158 (term243 _48286 _48287) (term173 _48287) (term243 _48286 _48287)). Qed.
Lemma lem4106930 (_48286 : int) (_48287 : int) : (term238 _48286 _48287) = (term242 _48286 _48287).
Proof. exact (TRANS (@lem4106922 _48286 _48287) (@lem4106929 _48286 _48287)). Qed.
Lemma lem4106933 (_48286 : int) : (term237 _48286) = (term237 _48286).
Proof. exact (eq_refl (term237 _48286)). Qed.
Lemma lem4106934 (_48286 : int) (_48287 : int) : (term239 _48286 _48287) = (term244 _48286 _48287).
Proof. exact (MK_COMB (@lem4106933 _48286) (@lem4106930 _48286 _48287)). Qed.
Lemma lem4106941 (_48286 : int) (_48287 : int) : (term244 _48286 _48287) = (term245 _48286 _48287).
Proof. exact (@lem19158 (term246 _48286 _48287) (term173 _48286) (term246 _48286 _48287)). Qed.
Lemma lem4106942 (_48286 : int) (_48287 : int) : (term239 _48286 _48287) = (term245 _48286 _48287).
Proof. exact (TRANS (@lem4106934 _48286 _48287) (@lem4106941 _48286 _48287)). Qed.
Lemma lem4106943 (_48286 : int) (_48287 : int) : (term142 _48286 _48287) = (term245 _48286 _48287).
Proof. exact (TRANS (@lem4106901 _48286 _48287) (@lem4106942 _48286 _48287)). Qed.
Lemma lem4106953 (_48286 : int) (_48287 : int) (h1 : term245 _48286 _48287) : term245 _48286 _48287.
Proof. exact (h1). Qed.
Lemma lem4106954 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term247 _48286 _48287.
Proof. exact (h1). Qed.
Lemma lem4106955 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term246 _48286 _48287.
Proof. exact (proj2 (@lem4106954 _48286 _48287 h1)). Qed.
Lemma lem4106957 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term243 _48286 _48287.
Proof. exact (proj2 (@lem4106955 _48286 _48287 h1)). Qed.
Lemma lem4106959 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term234 _48286 _48287.
Proof. exact (proj2 (@lem4106957 _48286 _48287 h1)). Qed.
Lemma lem4106960 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term179 _48286 _48287.
Proof. exact (proj1 (@lem4106957 _48286 _48287 h1)). Qed.
Lemma lem4106962 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4106963 : term248 = term208.
Proof. exact (@lem4106962 term111 term124). Qed.
Lemma lem4106965 (x : nat) : (real_of_num x) = (term149 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4106966 : term124 = term185.
Proof. exact (@lem4106965 term61). Qed.
Lemma lem4106968 (x : nat) : (real_of_num x) = (term149 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4106969 : term111 = term150.
Proof. exact (@lem4106968 (NUMERAL 0)). Qed.
Lemma lem4106970 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4106971 : term249 = term250.
Proof. exact (MK_COMB (@lem4106970) (@lem4106969)). Qed.
Lemma lem4106972 : term208 = term251.
Proof. exact (MK_COMB (@lem4106971) (@lem4106966)). Qed.
Lemma lem4106973 : term252.
Proof. exact (@lem1980255 term111 term124 term124 term124). Qed.
Lemma lem4106975 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4106976 : term208 = term209.
Proof. exact (@lem4106975 (NUMERAL 0) term61). Qed.
Lemma lem4106977 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4106978 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4106979 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4106978 h1) (fun h1 : term209 = True => @lem4106977)). Qed.
Lemma lem4106980 : term209 = True.
Proof. exact (EQ_MP (@lem4106979) (@lem4106977)). Qed.
Lemma lem4106981 : term208 = True.
Proof. exact (TRANS (@lem4106976) (@lem4106980)). Qed.
Lemma lem4106982 : True = term208.
Proof. exact (SYM (@lem4106981)). Qed.
Lemma lem4106983 : term208.
Proof. exact (EQ_MP (@lem4106982) (@lem0)). Qed.
Lemma lem4106984 : term253.
Proof. exact (@lem4106973 (@lem4106983)). Qed.
Lemma lem4106986 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4106987 : term208 = term209.
Proof. exact (@lem4106986 (NUMERAL 0) term61). Qed.
Lemma lem4106988 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4106989 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4106990 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4106989 h1) (fun h1 : term209 = True => @lem4106988)). Qed.
Lemma lem4106991 : term209 = True.
Proof. exact (EQ_MP (@lem4106990) (@lem4106988)). Qed.
Lemma lem4106992 : term208 = True.
Proof. exact (TRANS (@lem4106987) (@lem4106991)). Qed.
Lemma lem4106993 : True = term208.
Proof. exact (SYM (@lem4106992)). Qed.
Lemma lem4106994 : term208.
Proof. exact (EQ_MP (@lem4106993) (@lem0)). Qed.
Lemma lem4106995 : term251 = term254.
Proof. exact (@lem4106984 (@lem4106994)). Qed.
Lemma lem4106997 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4106998 : term162 = term163.
Proof. exact (@lem4106997 term61 term61). Qed.
Lemma lem4106999 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4107000 : term165 = term61.
Proof. exact (EQ_MP (@lem4106999) (@lem940073)). Qed.
Lemma lem4107001 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4107002 : term163 = term124.
Proof. exact (MK_COMB (@lem4107001) (@lem4107000)). Qed.
Lemma lem4107003 : term162 = term124.
Proof. exact (TRANS (@lem4106998) (@lem4107002)). Qed.
Lemma lem4107005 (x : nat) : (term221 x) = term111.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4107006 : term220 = term111.
Proof. exact (@lem4107005 term61). Qed.
Lemma lem4107007 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4107008 : term255 = term249.
Proof. exact (MK_COMB (@lem4107007) (@lem4107006)). Qed.
Lemma lem4107009 : term254 = term208.
Proof. exact (MK_COMB (@lem4107008) (@lem4107003)). Qed.
Lemma lem4107011 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107012 : term208 = term209.
Proof. exact (@lem4107011 (NUMERAL 0) term61). Qed.
Lemma lem4107013 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107014 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107015 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107014 h1) (fun h1 : term209 = True => @lem4107013)). Qed.
Lemma lem4107016 : term209 = True.
Proof. exact (EQ_MP (@lem4107015) (@lem4107013)). Qed.
Lemma lem4107017 : term208 = True.
Proof. exact (TRANS (@lem4107012) (@lem4107016)). Qed.
Lemma lem4107018 : term254 = True.
Proof. exact (TRANS (@lem4107009) (@lem4107017)). Qed.
Lemma lem4107019 : term251 = True.
Proof. exact (TRANS (@lem4106995) (@lem4107018)). Qed.
Lemma lem4107020 : term208 = True.
Proof. exact (TRANS (@lem4106972) (@lem4107019)). Qed.
Lemma lem4107021 : term248 = True.
Proof. exact (TRANS (@lem4106963) (@lem4107020)). Qed.
Lemma lem4107022 : True = term248.
Proof. exact (SYM (@lem4107021)). Qed.
Lemma lem4107023 : term248.
Proof. exact (EQ_MP (@lem4107022) (@lem0)). Qed.
Lemma lem4107024 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term256 _48286 _48287.
Proof. exact (conj (@lem4107023) (@lem4106960 _48286 _48287 h1)). Qed.
Lemma lem4107026 (x : real) (y : real) : term257 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4107027 (_48286 : int) (_48287 : int) : term258 _48286 _48287.
Proof. exact (@lem4107026 term124 (term176 _48286 _48287)). Qed.
Lemma lem4107028 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term259 _48286 _48287.
Proof. exact (@lem4107027 _48286 _48287 (@lem4107024 _48286 _48287 h1)). Qed.
Lemma lem4107029 (_48286 : int) (_48287 : int) : (term260 _48286 _48287) = (term176 _48286 _48287).
Proof. exact (@lem1982733 (term176 _48286 _48287)). Qed.
Lemma lem4107030 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4107031 (_48286 : int) (_48287 : int) : (term261 _48286 _48287) = (term178 _48286 _48287).
Proof. exact (MK_COMB (@lem4107030) (@lem4107029 _48286 _48287)). Qed.
Lemma lem4107032 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4107033 (_48286 : int) (_48287 : int) : (term259 _48286 _48287) = (term179 _48286 _48287).
Proof. exact (MK_COMB (@lem4107031 _48286 _48287) (@lem4107032)). Qed.
Lemma lem4107034 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term179 _48286 _48287.
Proof. exact (EQ_MP (@lem4107033 _48286 _48287) (@lem4107028 _48286 _48287 h1)). Qed.
Lemma lem4107036 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4107037 : term248 = term208.
Proof. exact (@lem4107036 term111 term124). Qed.
Lemma lem4107039 (x : nat) : (real_of_num x) = (term149 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4107040 : term124 = term185.
Proof. exact (@lem4107039 term61). Qed.
Lemma lem4107042 (x : nat) : (real_of_num x) = (term149 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4107043 : term111 = term150.
Proof. exact (@lem4107042 (NUMERAL 0)). Qed.
Lemma lem4107044 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4107045 : term249 = term250.
Proof. exact (MK_COMB (@lem4107044) (@lem4107043)). Qed.
Lemma lem4107046 : term208 = term251.
Proof. exact (MK_COMB (@lem4107045) (@lem4107040)). Qed.
Lemma lem4107047 : term252.
Proof. exact (@lem1980255 term111 term124 term124 term124). Qed.
Lemma lem4107049 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107050 : term208 = term209.
Proof. exact (@lem4107049 (NUMERAL 0) term61). Qed.
Lemma lem4107051 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107052 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107053 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107052 h1) (fun h1 : term209 = True => @lem4107051)). Qed.
Lemma lem4107054 : term209 = True.
Proof. exact (EQ_MP (@lem4107053) (@lem4107051)). Qed.
Lemma lem4107055 : term208 = True.
Proof. exact (TRANS (@lem4107050) (@lem4107054)). Qed.
Lemma lem4107056 : True = term208.
Proof. exact (SYM (@lem4107055)). Qed.
Lemma lem4107057 : term208.
Proof. exact (EQ_MP (@lem4107056) (@lem0)). Qed.
Lemma lem4107058 : term253.
Proof. exact (@lem4107047 (@lem4107057)). Qed.
Lemma lem4107060 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107061 : term208 = term209.
Proof. exact (@lem4107060 (NUMERAL 0) term61). Qed.
Lemma lem4107062 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107063 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107064 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107063 h1) (fun h1 : term209 = True => @lem4107062)). Qed.
Lemma lem4107065 : term209 = True.
Proof. exact (EQ_MP (@lem4107064) (@lem4107062)). Qed.
Lemma lem4107066 : term208 = True.
Proof. exact (TRANS (@lem4107061) (@lem4107065)). Qed.
Lemma lem4107067 : True = term208.
Proof. exact (SYM (@lem4107066)). Qed.
Lemma lem4107068 : term208.
Proof. exact (EQ_MP (@lem4107067) (@lem0)). Qed.
Lemma lem4107069 : term251 = term254.
Proof. exact (@lem4107058 (@lem4107068)). Qed.
Lemma lem4107071 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4107072 : term162 = term163.
Proof. exact (@lem4107071 term61 term61). Qed.
Lemma lem4107073 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4107074 : term165 = term61.
Proof. exact (EQ_MP (@lem4107073) (@lem940073)). Qed.
Lemma lem4107075 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4107076 : term163 = term124.
Proof. exact (MK_COMB (@lem4107075) (@lem4107074)). Qed.
Lemma lem4107077 : term162 = term124.
Proof. exact (TRANS (@lem4107072) (@lem4107076)). Qed.
Lemma lem4107079 (x : nat) : (term221 x) = term111.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4107080 : term220 = term111.
Proof. exact (@lem4107079 term61). Qed.
Lemma lem4107081 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4107082 : term255 = term249.
Proof. exact (MK_COMB (@lem4107081) (@lem4107080)). Qed.
Lemma lem4107083 : term254 = term208.
Proof. exact (MK_COMB (@lem4107082) (@lem4107077)). Qed.
Lemma lem4107085 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107086 : term208 = term209.
Proof. exact (@lem4107085 (NUMERAL 0) term61). Qed.
Lemma lem4107087 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107088 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107089 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107088 h1) (fun h1 : term209 = True => @lem4107087)). Qed.
Lemma lem4107090 : term209 = True.
Proof. exact (EQ_MP (@lem4107089) (@lem4107087)). Qed.
Lemma lem4107091 : term208 = True.
Proof. exact (TRANS (@lem4107086) (@lem4107090)). Qed.
Lemma lem4107092 : term254 = True.
Proof. exact (TRANS (@lem4107083) (@lem4107091)). Qed.
Lemma lem4107093 : term251 = True.
Proof. exact (TRANS (@lem4107069) (@lem4107092)). Qed.
Lemma lem4107094 : term208 = True.
Proof. exact (TRANS (@lem4107046) (@lem4107093)). Qed.
Lemma lem4107095 : term248 = True.
Proof. exact (TRANS (@lem4107037) (@lem4107094)). Qed.
Lemma lem4107096 : True = term248.
Proof. exact (SYM (@lem4107095)). Qed.
Lemma lem4107097 : term248.
Proof. exact (EQ_MP (@lem4107096) (@lem0)). Qed.
Lemma lem4107098 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term262 _48286 _48287.
Proof. exact (conj (@lem4107097) (@lem4106959 _48286 _48287 h1)). Qed.
Lemma lem4107100 (x : real) (y : real) : term257 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4107101 (_48286 : int) (_48287 : int) : term263 _48286 _48287.
Proof. exact (@lem4107100 term124 (term231 _48286 _48287)). Qed.
Lemma lem4107102 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term264 _48286 _48287.
Proof. exact (@lem4107101 _48286 _48287 (@lem4107098 _48286 _48287 h1)). Qed.
Lemma lem4107103 (_48286 : int) (_48287 : int) : (term265 _48286 _48287) = (term231 _48286 _48287).
Proof. exact (@lem1982733 (term231 _48286 _48287)). Qed.
Lemma lem4107104 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4107105 (_48286 : int) (_48287 : int) : (term266 _48286 _48287) = (term233 _48286 _48287).
Proof. exact (MK_COMB (@lem4107104) (@lem4107103 _48286 _48287)). Qed.
Lemma lem4107106 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4107107 (_48286 : int) (_48287 : int) : (term264 _48286 _48287) = (term234 _48286 _48287).
Proof. exact (MK_COMB (@lem4107105 _48286 _48287) (@lem4107106)). Qed.
Lemma lem4107108 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term234 _48286 _48287.
Proof. exact (EQ_MP (@lem4107107 _48286 _48287) (@lem4107102 _48286 _48287 h1)). Qed.
Lemma lem4107109 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term267 _48286 _48287.
Proof. exact (conj (@lem4107108 _48286 _48287 h1) (@lem4107034 _48286 _48287 h1)). Qed.
Lemma lem4107111 (x : real) (y : real) : term268 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem4107112 (_48286 : int) (_48287 : int) : term269 _48286 _48287.
Proof. exact (@lem4107111 (term231 _48286 _48287) (term176 _48286 _48287)). Qed.
Lemma lem4107113 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term270 _48286 _48287.
Proof. exact (@lem4107112 _48286 _48287 (@lem4107109 _48286 _48287 h1)). Qed.
Lemma lem4107114 (_48286 : int) (_48287 : int) : (term271 _48286 _48287) = (term272 _48286 _48287).
Proof. exact (@lem1982753 (term201 _48286) (real_of_int _48286) (term273 _48287) (term201 _48287)). Qed.
Lemma lem4107115 (_48286 : int) : (term274 _48286) = (term275 _48286).
Proof. exact (@lem1982713 term153 (real_of_int _48286)). Qed.
Lemma lem4107117 (x : nat) : (real_of_num x) = (term149 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4107118 : term124 = term185.
Proof. exact (@lem4107117 term61). Qed.
Lemma lem4107120 (x : nat) : (term151 x) = (term152 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4107121 : term153 = term154.
Proof. exact (@lem4107120 term61). Qed.
Lemma lem4107122 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4107123 : term276 = term277.
Proof. exact (MK_COMB (@lem4107122) (@lem4107121)). Qed.
Lemma lem4107124 : term278 = term279.
Proof. exact (MK_COMB (@lem4107123) (@lem4107118)). Qed.
Lemma lem4107125 : term280.
Proof. exact (@lem1981473 term153 term124 term124 term124 term111 term124). Qed.
Lemma lem4107127 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107128 : term208 = term209.
Proof. exact (@lem4107127 (NUMERAL 0) term61). Qed.
Lemma lem4107129 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107130 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107131 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107130 h1) (fun h1 : term209 = True => @lem4107129)). Qed.
Lemma lem4107132 : term209 = True.
Proof. exact (EQ_MP (@lem4107131) (@lem4107129)). Qed.
Lemma lem4107133 : term208 = True.
Proof. exact (TRANS (@lem4107128) (@lem4107132)). Qed.
Lemma lem4107134 : True = term208.
Proof. exact (SYM (@lem4107133)). Qed.
Lemma lem4107135 : term208.
Proof. exact (EQ_MP (@lem4107134) (@lem0)). Qed.
Lemma lem4107136 : term281.
Proof. exact (@lem4107125 (@lem4107135)). Qed.
Lemma lem4107138 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107139 : term208 = term209.
Proof. exact (@lem4107138 (NUMERAL 0) term61). Qed.
Lemma lem4107140 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107141 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107142 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107141 h1) (fun h1 : term209 = True => @lem4107140)). Qed.
Lemma lem4107143 : term209 = True.
Proof. exact (EQ_MP (@lem4107142) (@lem4107140)). Qed.
Lemma lem4107144 : term208 = True.
Proof. exact (TRANS (@lem4107139) (@lem4107143)). Qed.
Lemma lem4107145 : True = term208.
Proof. exact (SYM (@lem4107144)). Qed.
Lemma lem4107146 : term208.
Proof. exact (EQ_MP (@lem4107145) (@lem0)). Qed.
Lemma lem4107147 : term282.
Proof. exact (@lem4107136 (@lem4107146)). Qed.
Lemma lem4107149 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107150 : term208 = term209.
Proof. exact (@lem4107149 (NUMERAL 0) term61). Qed.
Lemma lem4107151 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107152 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107153 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107152 h1) (fun h1 : term209 = True => @lem4107151)). Qed.
Lemma lem4107154 : term209 = True.
Proof. exact (EQ_MP (@lem4107153) (@lem4107151)). Qed.
Lemma lem4107155 : term208 = True.
Proof. exact (TRANS (@lem4107150) (@lem4107154)). Qed.
Lemma lem4107156 : True = term208.
Proof. exact (SYM (@lem4107155)). Qed.
Lemma lem4107157 : term208.
Proof. exact (EQ_MP (@lem4107156) (@lem0)). Qed.
Lemma lem4107158 : term283.
Proof. exact (@lem4107147 (@lem4107157)). Qed.
Lemma lem4107160 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4107161 : term162 = term163.
Proof. exact (@lem4107160 term61 term61). Qed.
Lemma lem4107162 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4107163 : term165 = term61.
Proof. exact (EQ_MP (@lem4107162) (@lem940073)). Qed.
Lemma lem4107164 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4107165 : term163 = term124.
Proof. exact (MK_COMB (@lem4107164) (@lem4107163)). Qed.
Lemma lem4107166 : term162 = term124.
Proof. exact (TRANS (@lem4107161) (@lem4107165)). Qed.
Lemma lem4107168 (m : nat) (n : nat) : (term189 m n) = (term190 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4107169 : term186 = term191.
Proof. exact (@lem4107168 term61 term61). Qed.
Lemma lem4107170 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4107171 : term165 = term61.
Proof. exact (EQ_MP (@lem4107170) (@lem940073)). Qed.
Lemma lem4107172 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4107173 : term163 = term124.
Proof. exact (MK_COMB (@lem4107172) (@lem4107171)). Qed.
Lemma lem4107174 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4107175 : term191 = term153.
Proof. exact (MK_COMB (@lem4107174) (@lem4107173)). Qed.
Lemma lem4107176 : term186 = term153.
Proof. exact (TRANS (@lem4107169) (@lem4107175)). Qed.
Lemma lem4107177 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4107178 : term284 = term276.
Proof. exact (MK_COMB (@lem4107177) (@lem4107176)). Qed.
Lemma lem4107179 : term285 = term278.
Proof. exact (MK_COMB (@lem4107178) (@lem4107166)). Qed.
Lemma lem4107181 (m : nat) : (term286 m) = term111.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4107182 : term278 = term111.
Proof. exact (@lem4107181 term61). Qed.
Lemma lem4107183 : term285 = term111.
Proof. exact (TRANS (@lem4107179) (@lem4107182)). Qed.
Lemma lem4107184 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4107185 : term287 = term218.
Proof. exact (MK_COMB (@lem4107184) (@lem4107183)). Qed.
Lemma lem4107186 : term124 = term124.
Proof. exact (eq_refl term124). Qed.
Lemma lem4107187 : term288 = term220.
Proof. exact (MK_COMB (@lem4107185) (@lem4107186)). Qed.
Lemma lem4107189 (x : nat) : (term221 x) = term111.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4107190 : term220 = term111.
Proof. exact (@lem4107189 term61). Qed.
Lemma lem4107191 : term288 = term111.
Proof. exact (TRANS (@lem4107187) (@lem4107190)). Qed.
Lemma lem4107193 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4107194 : term162 = term163.
Proof. exact (@lem4107193 term61 term61). Qed.
Lemma lem4107195 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4107196 : term165 = term61.
Proof. exact (EQ_MP (@lem4107195) (@lem940073)). Qed.
Lemma lem4107197 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4107198 : term163 = term124.
Proof. exact (MK_COMB (@lem4107197) (@lem4107196)). Qed.
Lemma lem4107199 : term162 = term124.
Proof. exact (TRANS (@lem4107194) (@lem4107198)). Qed.
Lemma lem4107200 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem4107201 : term222 = term220.
Proof. exact (MK_COMB (@lem4107200) (@lem4107199)). Qed.
Lemma lem4107203 (x : nat) : (term221 x) = term111.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4107204 : term220 = term111.
Proof. exact (@lem4107203 term61). Qed.
Lemma lem4107205 : term222 = term111.
Proof. exact (TRANS (@lem4107201) (@lem4107204)). Qed.
Lemma lem4107206 : term111 = term222.
Proof. exact (SYM (@lem4107205)). Qed.
Lemma lem4107207 : term288 = term222.
Proof. exact (TRANS (@lem4107191) (@lem4107206)). Qed.
Lemma lem4107208 : term279 = term150.
Proof. exact (@lem4107158 (@lem4107207)). Qed.
Lemma lem4107209 : term278 = term150.
Proof. exact (TRANS (@lem4107124) (@lem4107208)). Qed.
Lemma lem4107211 (x : real) : (term169 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4107212 : term150 = term111.
Proof. exact (@lem4107211 term111). Qed.
Lemma lem4107213 : term278 = term111.
Proof. exact (TRANS (@lem4107209) (@lem4107212)). Qed.
Lemma lem4107214 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4107215 : term289 = term218.
Proof. exact (MK_COMB (@lem4107214) (@lem4107213)). Qed.
Lemma lem4107216 (_48286 : int) : (real_of_int _48286) = (real_of_int _48286).
Proof. exact (eq_refl (real_of_int _48286)). Qed.
Lemma lem4107217 (_48286 : int) : (term275 _48286) = (term290 _48286).
Proof. exact (MK_COMB (@lem4107215) (@lem4107216 _48286)). Qed.
Lemma lem4107218 (_48286 : int) : (term274 _48286) = (term290 _48286).
Proof. exact (TRANS (@lem4107115 _48286) (@lem4107217 _48286)). Qed.
Lemma lem4107219 (_48286 : int) : (term290 _48286) = term111.
Proof. exact (@lem1982719 (real_of_int _48286)). Qed.
Lemma lem4107220 (_48286 : int) : (term274 _48286) = term111.
Proof. exact (TRANS (@lem4107218 _48286) (@lem4107219 _48286)). Qed.
Lemma lem4107221 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4107222 (_48286 : int) : (term291 _48286) = term292.
Proof. exact (MK_COMB (@lem4107221) (@lem4107220 _48286)). Qed.
Lemma lem4107223 (_48287 : int) : (term293 _48287) = (term294 _48287).
Proof. exact (@lem1982759 (real_of_int _48287) (term201 _48287) term153). Qed.
Lemma lem4107224 (_48287 : int) : (term295 _48287) = (term275 _48287).
Proof. exact (@lem1982715 term153 (real_of_int _48287)). Qed.
Lemma lem4107226 (x : nat) : (real_of_num x) = (term149 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4107227 : term124 = term185.
Proof. exact (@lem4107226 term61). Qed.
Lemma lem4107229 (x : nat) : (term151 x) = (term152 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4107230 : term153 = term154.
Proof. exact (@lem4107229 term61). Qed.
Lemma lem4107231 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4107232 : term276 = term277.
Proof. exact (MK_COMB (@lem4107231) (@lem4107230)). Qed.
Lemma lem4107233 : term278 = term279.
Proof. exact (MK_COMB (@lem4107232) (@lem4107227)). Qed.
Lemma lem4107234 : term280.
Proof. exact (@lem1981473 term153 term124 term124 term124 term111 term124). Qed.
Lemma lem4107236 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107237 : term208 = term209.
Proof. exact (@lem4107236 (NUMERAL 0) term61). Qed.
Lemma lem4107238 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107239 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107240 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107239 h1) (fun h1 : term209 = True => @lem4107238)). Qed.
Lemma lem4107241 : term209 = True.
Proof. exact (EQ_MP (@lem4107240) (@lem4107238)). Qed.
Lemma lem4107242 : term208 = True.
Proof. exact (TRANS (@lem4107237) (@lem4107241)). Qed.
Lemma lem4107243 : True = term208.
Proof. exact (SYM (@lem4107242)). Qed.
Lemma lem4107244 : term208.
Proof. exact (EQ_MP (@lem4107243) (@lem0)). Qed.
Lemma lem4107245 : term281.
Proof. exact (@lem4107234 (@lem4107244)). Qed.
Lemma lem4107247 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107248 : term208 = term209.
Proof. exact (@lem4107247 (NUMERAL 0) term61). Qed.
Lemma lem4107249 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107250 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107251 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107250 h1) (fun h1 : term209 = True => @lem4107249)). Qed.
Lemma lem4107252 : term209 = True.
Proof. exact (EQ_MP (@lem4107251) (@lem4107249)). Qed.
Lemma lem4107253 : term208 = True.
Proof. exact (TRANS (@lem4107248) (@lem4107252)). Qed.
Lemma lem4107254 : True = term208.
Proof. exact (SYM (@lem4107253)). Qed.
Lemma lem4107255 : term208.
Proof. exact (EQ_MP (@lem4107254) (@lem0)). Qed.
Lemma lem4107256 : term282.
Proof. exact (@lem4107245 (@lem4107255)). Qed.
Lemma lem4107258 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107259 : term208 = term209.
Proof. exact (@lem4107258 (NUMERAL 0) term61). Qed.
Lemma lem4107260 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107261 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107262 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107261 h1) (fun h1 : term209 = True => @lem4107260)). Qed.
Lemma lem4107263 : term209 = True.
Proof. exact (EQ_MP (@lem4107262) (@lem4107260)). Qed.
Lemma lem4107264 : term208 = True.
Proof. exact (TRANS (@lem4107259) (@lem4107263)). Qed.
Lemma lem4107265 : True = term208.
Proof. exact (SYM (@lem4107264)). Qed.
Lemma lem4107266 : term208.
Proof. exact (EQ_MP (@lem4107265) (@lem0)). Qed.
Lemma lem4107267 : term283.
Proof. exact (@lem4107256 (@lem4107266)). Qed.
Lemma lem4107269 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4107270 : term162 = term163.
Proof. exact (@lem4107269 term61 term61). Qed.
Lemma lem4107271 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4107272 : term165 = term61.
Proof. exact (EQ_MP (@lem4107271) (@lem940073)). Qed.
Lemma lem4107273 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4107274 : term163 = term124.
Proof. exact (MK_COMB (@lem4107273) (@lem4107272)). Qed.
Lemma lem4107275 : term162 = term124.
Proof. exact (TRANS (@lem4107270) (@lem4107274)). Qed.
Lemma lem4107277 (m : nat) (n : nat) : (term189 m n) = (term190 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4107278 : term186 = term191.
Proof. exact (@lem4107277 term61 term61). Qed.
Lemma lem4107279 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4107280 : term165 = term61.
Proof. exact (EQ_MP (@lem4107279) (@lem940073)). Qed.
Lemma lem4107281 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4107282 : term163 = term124.
Proof. exact (MK_COMB (@lem4107281) (@lem4107280)). Qed.
Lemma lem4107283 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4107284 : term191 = term153.
Proof. exact (MK_COMB (@lem4107283) (@lem4107282)). Qed.
Lemma lem4107285 : term186 = term153.
Proof. exact (TRANS (@lem4107278) (@lem4107284)). Qed.
Lemma lem4107286 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4107287 : term284 = term276.
Proof. exact (MK_COMB (@lem4107286) (@lem4107285)). Qed.
Lemma lem4107288 : term285 = term278.
Proof. exact (MK_COMB (@lem4107287) (@lem4107275)). Qed.
Lemma lem4107290 (m : nat) : (term286 m) = term111.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4107291 : term278 = term111.
Proof. exact (@lem4107290 term61). Qed.
Lemma lem4107292 : term285 = term111.
Proof. exact (TRANS (@lem4107288) (@lem4107291)). Qed.
Lemma lem4107293 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4107294 : term287 = term218.
Proof. exact (MK_COMB (@lem4107293) (@lem4107292)). Qed.
Lemma lem4107295 : term124 = term124.
Proof. exact (eq_refl term124). Qed.
Lemma lem4107296 : term288 = term220.
Proof. exact (MK_COMB (@lem4107294) (@lem4107295)). Qed.
Lemma lem4107298 (x : nat) : (term221 x) = term111.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4107299 : term220 = term111.
Proof. exact (@lem4107298 term61). Qed.
Lemma lem4107300 : term288 = term111.
Proof. exact (TRANS (@lem4107296) (@lem4107299)). Qed.
Lemma lem4107302 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4107303 : term162 = term163.
Proof. exact (@lem4107302 term61 term61). Qed.
Lemma lem4107304 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4107305 : term165 = term61.
Proof. exact (EQ_MP (@lem4107304) (@lem940073)). Qed.
Lemma lem4107306 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4107307 : term163 = term124.
Proof. exact (MK_COMB (@lem4107306) (@lem4107305)). Qed.
Lemma lem4107308 : term162 = term124.
Proof. exact (TRANS (@lem4107303) (@lem4107307)). Qed.
Lemma lem4107309 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem4107310 : term222 = term220.
Proof. exact (MK_COMB (@lem4107309) (@lem4107308)). Qed.
Lemma lem4107312 (x : nat) : (term221 x) = term111.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4107313 : term220 = term111.
Proof. exact (@lem4107312 term61). Qed.
Lemma lem4107314 : term222 = term111.
Proof. exact (TRANS (@lem4107310) (@lem4107313)). Qed.
Lemma lem4107315 : term111 = term222.
Proof. exact (SYM (@lem4107314)). Qed.
Lemma lem4107316 : term288 = term222.
Proof. exact (TRANS (@lem4107300) (@lem4107315)). Qed.
Lemma lem4107317 : term279 = term150.
Proof. exact (@lem4107267 (@lem4107316)). Qed.
Lemma lem4107318 : term278 = term150.
Proof. exact (TRANS (@lem4107233) (@lem4107317)). Qed.
Lemma lem4107320 (x : real) : (term169 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4107321 : term150 = term111.
Proof. exact (@lem4107320 term111). Qed.
Lemma lem4107322 : term278 = term111.
Proof. exact (TRANS (@lem4107318) (@lem4107321)). Qed.
Lemma lem4107323 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4107324 : term289 = term218.
Proof. exact (MK_COMB (@lem4107323) (@lem4107322)). Qed.
Lemma lem4107325 (_48287 : int) : (real_of_int _48287) = (real_of_int _48287).
Proof. exact (eq_refl (real_of_int _48287)). Qed.
Lemma lem4107326 (_48287 : int) : (term275 _48287) = (term290 _48287).
Proof. exact (MK_COMB (@lem4107324) (@lem4107325 _48287)). Qed.
Lemma lem4107327 (_48287 : int) : (term295 _48287) = (term290 _48287).
Proof. exact (TRANS (@lem4107224 _48287) (@lem4107326 _48287)). Qed.
Lemma lem4107328 (_48287 : int) : (term290 _48287) = term111.
Proof. exact (@lem1982719 (real_of_int _48287)). Qed.
Lemma lem4107329 (_48287 : int) : (term295 _48287) = term111.
Proof. exact (TRANS (@lem4107327 _48287) (@lem4107328 _48287)). Qed.
Lemma lem4107330 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4107331 (_48287 : int) : (term296 _48287) = term292.
Proof. exact (MK_COMB (@lem4107330) (@lem4107329 _48287)). Qed.
Lemma lem4107332 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem4107333 (_48287 : int) : (term294 _48287) = term297.
Proof. exact (MK_COMB (@lem4107331 _48287) (@lem4107332)). Qed.
Lemma lem4107334 (_48287 : int) : (term293 _48287) = term297.
Proof. exact (TRANS (@lem4107223 _48287) (@lem4107333 _48287)). Qed.
Lemma lem4107335 : term297 = term153.
Proof. exact (@lem1982721 term153). Qed.
Lemma lem4107336 (_48287 : int) : (term293 _48287) = term153.
Proof. exact (TRANS (@lem4107334 _48287) (@lem4107335)). Qed.
Lemma lem4107337 (_48286 : int) (_48287 : int) : (term272 _48286 _48287) = term297.
Proof. exact (MK_COMB (@lem4107222 _48286) (@lem4107336 _48287)). Qed.
Lemma lem4107338 (_48286 : int) (_48287 : int) : (term271 _48286 _48287) = term297.
Proof. exact (TRANS (@lem4107114 _48286 _48287) (@lem4107337 _48286 _48287)). Qed.
Lemma lem4107339 : term297 = term153.
Proof. exact (@lem1982721 term153). Qed.
Lemma lem4107340 (_48286 : int) (_48287 : int) : (term271 _48286 _48287) = term153.
Proof. exact (TRANS (@lem4107338 _48286 _48287) (@lem4107339)). Qed.
Lemma lem4107341 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4107342 (_48286 : int) (_48287 : int) : (term298 _48286 _48287) = term299.
Proof. exact (MK_COMB (@lem4107341) (@lem4107340 _48286 _48287)). Qed.
Lemma lem4107343 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4107344 (_48286 : int) (_48287 : int) : (term270 _48286 _48287) = term300.
Proof. exact (MK_COMB (@lem4107342 _48286 _48287) (@lem4107343)). Qed.
Lemma lem4107345 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term300.
Proof. exact (EQ_MP (@lem4107344 _48286 _48287) (@lem4107113 _48286 _48287 h1)). Qed.
Lemma lem4107347 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4107348 : term300 = term301.
Proof. exact (@lem4107347 term111 term153). Qed.
Lemma lem4107350 (x : nat) : (term151 x) = (term152 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4107351 : term153 = term154.
Proof. exact (@lem4107350 term61). Qed.
Lemma lem4107353 (x : nat) : (real_of_num x) = (term149 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4107354 : term111 = term150.
Proof. exact (@lem4107353 (NUMERAL 0)). Qed.
Lemma lem4107355 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4107356 : term113 = term302.
Proof. exact (MK_COMB (@lem4107355) (@lem4107354)). Qed.
Lemma lem4107357 : term301 = term303.
Proof. exact (MK_COMB (@lem4107356) (@lem4107351)). Qed.
Lemma lem4107358 : term304.
Proof. exact (@lem1980026 term111 term124 term153 term124). Qed.
Lemma lem4107360 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107361 : term208 = term209.
Proof. exact (@lem4107360 (NUMERAL 0) term61). Qed.
Lemma lem4107362 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107363 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107364 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107363 h1) (fun h1 : term209 = True => @lem4107362)). Qed.
Lemma lem4107365 : term209 = True.
Proof. exact (EQ_MP (@lem4107364) (@lem4107362)). Qed.
Lemma lem4107366 : term208 = True.
Proof. exact (TRANS (@lem4107361) (@lem4107365)). Qed.
Lemma lem4107367 : True = term208.
Proof. exact (SYM (@lem4107366)). Qed.
Lemma lem4107368 : term208.
Proof. exact (EQ_MP (@lem4107367) (@lem0)). Qed.
Lemma lem4107369 : term305.
Proof. exact (@lem4107358 (@lem4107368)). Qed.
Lemma lem4107371 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107372 : term208 = term209.
Proof. exact (@lem4107371 (NUMERAL 0) term61). Qed.
Lemma lem4107373 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107374 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107375 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107374 h1) (fun h1 : term209 = True => @lem4107373)). Qed.
Lemma lem4107376 : term209 = True.
Proof. exact (EQ_MP (@lem4107375) (@lem4107373)). Qed.
Lemma lem4107377 : term208 = True.
Proof. exact (TRANS (@lem4107372) (@lem4107376)). Qed.
Lemma lem4107378 : True = term208.
Proof. exact (SYM (@lem4107377)). Qed.
Lemma lem4107379 : term208.
Proof. exact (EQ_MP (@lem4107378) (@lem0)). Qed.
Lemma lem4107380 : term303 = term306.
Proof. exact (@lem4107369 (@lem4107379)). Qed.
Lemma lem4107382 (m : nat) (n : nat) : (term189 m n) = (term190 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4107383 : term186 = term191.
Proof. exact (@lem4107382 term61 term61). Qed.
Lemma lem4107384 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4107385 : term165 = term61.
Proof. exact (EQ_MP (@lem4107384) (@lem940073)). Qed.
Lemma lem4107386 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4107387 : term163 = term124.
Proof. exact (MK_COMB (@lem4107386) (@lem4107385)). Qed.
Lemma lem4107388 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4107389 : term191 = term153.
Proof. exact (MK_COMB (@lem4107388) (@lem4107387)). Qed.
Lemma lem4107390 : term186 = term153.
Proof. exact (TRANS (@lem4107383) (@lem4107389)). Qed.
Lemma lem4107392 (x : nat) : (term221 x) = term111.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4107393 : term220 = term111.
Proof. exact (@lem4107392 term61). Qed.
Lemma lem4107394 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4107395 : term307 = term113.
Proof. exact (MK_COMB (@lem4107394) (@lem4107393)). Qed.
Lemma lem4107396 : term306 = term301.
Proof. exact (MK_COMB (@lem4107395) (@lem4107390)). Qed.
Lemma lem4107398 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4107399 : term301 = term310.
Proof. exact (@lem4107398 (NUMERAL 0) term61). Qed.
Lemma lem4107400 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107401 (h1 : term210 = (BIT1 0)) : (term61 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem4107402 : (term210 = (BIT1 0)) = ((term61 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107401 h1) (fun h1 : (term61 = (NUMERAL 0)) = False => @lem4107400)). Qed.
Lemma lem4107403 : (term61 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4107402) (@lem4107400)). Qed.
Lemma lem4107404 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4107405 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4107406 : term311 = (and True).
Proof. exact (MK_COMB (@lem4107405) (@lem4107404)). Qed.
Lemma lem4107407 : term310 = (True /\ False).
Proof. exact (MK_COMB (@lem4107406) (@lem4107403)). Qed.
Lemma lem4107409 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4107410 : term310 = False.
Proof. exact (TRANS (@lem4107407) (@lem4107409)). Qed.
Lemma lem4107411 : term301 = False.
Proof. exact (TRANS (@lem4107399) (@lem4107410)). Qed.
Lemma lem4107412 : term306 = False.
Proof. exact (TRANS (@lem4107396) (@lem4107411)). Qed.
Lemma lem4107413 : term303 = False.
Proof. exact (TRANS (@lem4107380) (@lem4107412)). Qed.
Lemma lem4107414 : term301 = False.
Proof. exact (TRANS (@lem4107357) (@lem4107413)). Qed.
Lemma lem4107415 : term300 = False.
Proof. exact (TRANS (@lem4107348) (@lem4107414)). Qed.
Lemma lem4107416 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : False.
Proof. exact (EQ_MP (@lem4107415) (@lem4107345 _48286 _48287 h1)). Qed.
Lemma lem4107417 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term247 _48286 _48287.
Proof. exact (h1). Qed.
Lemma lem4107418 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term246 _48286 _48287.
Proof. exact (proj2 (@lem4107417 _48286 _48287 h1)). Qed.
Lemma lem4107420 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term243 _48286 _48287.
Proof. exact (proj2 (@lem4107418 _48286 _48287 h1)). Qed.
Lemma lem4107422 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term234 _48286 _48287.
Proof. exact (proj2 (@lem4107420 _48286 _48287 h1)). Qed.
Lemma lem4107423 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term179 _48286 _48287.
Proof. exact (proj1 (@lem4107420 _48286 _48287 h1)). Qed.
Lemma lem4107425 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4107426 : term248 = term208.
Proof. exact (@lem4107425 term111 term124). Qed.
Lemma lem4107428 (x : nat) : (real_of_num x) = (term149 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4107429 : term124 = term185.
Proof. exact (@lem4107428 term61). Qed.
Lemma lem4107431 (x : nat) : (real_of_num x) = (term149 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4107432 : term111 = term150.
Proof. exact (@lem4107431 (NUMERAL 0)). Qed.
Lemma lem4107433 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4107434 : term249 = term250.
Proof. exact (MK_COMB (@lem4107433) (@lem4107432)). Qed.
Lemma lem4107435 : term208 = term251.
Proof. exact (MK_COMB (@lem4107434) (@lem4107429)). Qed.
Lemma lem4107436 : term252.
Proof. exact (@lem1980255 term111 term124 term124 term124). Qed.
Lemma lem4107438 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107439 : term208 = term209.
Proof. exact (@lem4107438 (NUMERAL 0) term61). Qed.
Lemma lem4107440 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107441 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107442 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107441 h1) (fun h1 : term209 = True => @lem4107440)). Qed.
Lemma lem4107443 : term209 = True.
Proof. exact (EQ_MP (@lem4107442) (@lem4107440)). Qed.
Lemma lem4107444 : term208 = True.
Proof. exact (TRANS (@lem4107439) (@lem4107443)). Qed.
Lemma lem4107445 : True = term208.
Proof. exact (SYM (@lem4107444)). Qed.
Lemma lem4107446 : term208.
Proof. exact (EQ_MP (@lem4107445) (@lem0)). Qed.
Lemma lem4107447 : term253.
Proof. exact (@lem4107436 (@lem4107446)). Qed.
Lemma lem4107449 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107450 : term208 = term209.
Proof. exact (@lem4107449 (NUMERAL 0) term61). Qed.
Lemma lem4107451 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107452 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107453 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107452 h1) (fun h1 : term209 = True => @lem4107451)). Qed.
Lemma lem4107454 : term209 = True.
Proof. exact (EQ_MP (@lem4107453) (@lem4107451)). Qed.
Lemma lem4107455 : term208 = True.
Proof. exact (TRANS (@lem4107450) (@lem4107454)). Qed.
Lemma lem4107456 : True = term208.
Proof. exact (SYM (@lem4107455)). Qed.
Lemma lem4107457 : term208.
Proof. exact (EQ_MP (@lem4107456) (@lem0)). Qed.
Lemma lem4107458 : term251 = term254.
Proof. exact (@lem4107447 (@lem4107457)). Qed.
Lemma lem4107460 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4107461 : term162 = term163.
Proof. exact (@lem4107460 term61 term61). Qed.
Lemma lem4107462 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4107463 : term165 = term61.
Proof. exact (EQ_MP (@lem4107462) (@lem940073)). Qed.
Lemma lem4107464 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4107465 : term163 = term124.
Proof. exact (MK_COMB (@lem4107464) (@lem4107463)). Qed.
Lemma lem4107466 : term162 = term124.
Proof. exact (TRANS (@lem4107461) (@lem4107465)). Qed.
Lemma lem4107468 (x : nat) : (term221 x) = term111.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4107469 : term220 = term111.
Proof. exact (@lem4107468 term61). Qed.
Lemma lem4107470 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4107471 : term255 = term249.
Proof. exact (MK_COMB (@lem4107470) (@lem4107469)). Qed.
Lemma lem4107472 : term254 = term208.
Proof. exact (MK_COMB (@lem4107471) (@lem4107466)). Qed.
Lemma lem4107474 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107475 : term208 = term209.
Proof. exact (@lem4107474 (NUMERAL 0) term61). Qed.
Lemma lem4107476 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107477 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107478 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107477 h1) (fun h1 : term209 = True => @lem4107476)). Qed.
Lemma lem4107479 : term209 = True.
Proof. exact (EQ_MP (@lem4107478) (@lem4107476)). Qed.
Lemma lem4107480 : term208 = True.
Proof. exact (TRANS (@lem4107475) (@lem4107479)). Qed.
Lemma lem4107481 : term254 = True.
Proof. exact (TRANS (@lem4107472) (@lem4107480)). Qed.
Lemma lem4107482 : term251 = True.
Proof. exact (TRANS (@lem4107458) (@lem4107481)). Qed.
Lemma lem4107483 : term208 = True.
Proof. exact (TRANS (@lem4107435) (@lem4107482)). Qed.
Lemma lem4107484 : term248 = True.
Proof. exact (TRANS (@lem4107426) (@lem4107483)). Qed.
Lemma lem4107485 : True = term248.
Proof. exact (SYM (@lem4107484)). Qed.
Lemma lem4107486 : term248.
Proof. exact (EQ_MP (@lem4107485) (@lem0)). Qed.
Lemma lem4107487 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term256 _48286 _48287.
Proof. exact (conj (@lem4107486) (@lem4107423 _48286 _48287 h1)). Qed.
Lemma lem4107489 (x : real) (y : real) : term257 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4107490 (_48286 : int) (_48287 : int) : term258 _48286 _48287.
Proof. exact (@lem4107489 term124 (term176 _48286 _48287)). Qed.
Lemma lem4107491 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term259 _48286 _48287.
Proof. exact (@lem4107490 _48286 _48287 (@lem4107487 _48286 _48287 h1)). Qed.
Lemma lem4107492 (_48286 : int) (_48287 : int) : (term260 _48286 _48287) = (term176 _48286 _48287).
Proof. exact (@lem1982733 (term176 _48286 _48287)). Qed.
Lemma lem4107493 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4107494 (_48286 : int) (_48287 : int) : (term261 _48286 _48287) = (term178 _48286 _48287).
Proof. exact (MK_COMB (@lem4107493) (@lem4107492 _48286 _48287)). Qed.
Lemma lem4107495 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4107496 (_48286 : int) (_48287 : int) : (term259 _48286 _48287) = (term179 _48286 _48287).
Proof. exact (MK_COMB (@lem4107494 _48286 _48287) (@lem4107495)). Qed.
Lemma lem4107497 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term179 _48286 _48287.
Proof. exact (EQ_MP (@lem4107496 _48286 _48287) (@lem4107491 _48286 _48287 h1)). Qed.
Lemma lem4107499 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4107500 : term248 = term208.
Proof. exact (@lem4107499 term111 term124). Qed.
Lemma lem4107502 (x : nat) : (real_of_num x) = (term149 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4107503 : term124 = term185.
Proof. exact (@lem4107502 term61). Qed.
Lemma lem4107505 (x : nat) : (real_of_num x) = (term149 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4107506 : term111 = term150.
Proof. exact (@lem4107505 (NUMERAL 0)). Qed.
Lemma lem4107507 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4107508 : term249 = term250.
Proof. exact (MK_COMB (@lem4107507) (@lem4107506)). Qed.
Lemma lem4107509 : term208 = term251.
Proof. exact (MK_COMB (@lem4107508) (@lem4107503)). Qed.
Lemma lem4107510 : term252.
Proof. exact (@lem1980255 term111 term124 term124 term124). Qed.
Lemma lem4107512 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107513 : term208 = term209.
Proof. exact (@lem4107512 (NUMERAL 0) term61). Qed.
Lemma lem4107514 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107515 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107516 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107515 h1) (fun h1 : term209 = True => @lem4107514)). Qed.
Lemma lem4107517 : term209 = True.
Proof. exact (EQ_MP (@lem4107516) (@lem4107514)). Qed.
Lemma lem4107518 : term208 = True.
Proof. exact (TRANS (@lem4107513) (@lem4107517)). Qed.
Lemma lem4107519 : True = term208.
Proof. exact (SYM (@lem4107518)). Qed.
Lemma lem4107520 : term208.
Proof. exact (EQ_MP (@lem4107519) (@lem0)). Qed.
Lemma lem4107521 : term253.
Proof. exact (@lem4107510 (@lem4107520)). Qed.
Lemma lem4107523 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107524 : term208 = term209.
Proof. exact (@lem4107523 (NUMERAL 0) term61). Qed.
Lemma lem4107525 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107526 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107527 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107526 h1) (fun h1 : term209 = True => @lem4107525)). Qed.
Lemma lem4107528 : term209 = True.
Proof. exact (EQ_MP (@lem4107527) (@lem4107525)). Qed.
Lemma lem4107529 : term208 = True.
Proof. exact (TRANS (@lem4107524) (@lem4107528)). Qed.
Lemma lem4107530 : True = term208.
Proof. exact (SYM (@lem4107529)). Qed.
Lemma lem4107531 : term208.
Proof. exact (EQ_MP (@lem4107530) (@lem0)). Qed.
Lemma lem4107532 : term251 = term254.
Proof. exact (@lem4107521 (@lem4107531)). Qed.
Lemma lem4107534 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4107535 : term162 = term163.
Proof. exact (@lem4107534 term61 term61). Qed.
Lemma lem4107536 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4107537 : term165 = term61.
Proof. exact (EQ_MP (@lem4107536) (@lem940073)). Qed.
Lemma lem4107538 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4107539 : term163 = term124.
Proof. exact (MK_COMB (@lem4107538) (@lem4107537)). Qed.
Lemma lem4107540 : term162 = term124.
Proof. exact (TRANS (@lem4107535) (@lem4107539)). Qed.
Lemma lem4107542 (x : nat) : (term221 x) = term111.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4107543 : term220 = term111.
Proof. exact (@lem4107542 term61). Qed.
Lemma lem4107544 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4107545 : term255 = term249.
Proof. exact (MK_COMB (@lem4107544) (@lem4107543)). Qed.
Lemma lem4107546 : term254 = term208.
Proof. exact (MK_COMB (@lem4107545) (@lem4107540)). Qed.
Lemma lem4107548 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107549 : term208 = term209.
Proof. exact (@lem4107548 (NUMERAL 0) term61). Qed.
Lemma lem4107550 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107551 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107552 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107551 h1) (fun h1 : term209 = True => @lem4107550)). Qed.
Lemma lem4107553 : term209 = True.
Proof. exact (EQ_MP (@lem4107552) (@lem4107550)). Qed.
Lemma lem4107554 : term208 = True.
Proof. exact (TRANS (@lem4107549) (@lem4107553)). Qed.
Lemma lem4107555 : term254 = True.
Proof. exact (TRANS (@lem4107546) (@lem4107554)). Qed.
Lemma lem4107556 : term251 = True.
Proof. exact (TRANS (@lem4107532) (@lem4107555)). Qed.
Lemma lem4107557 : term208 = True.
Proof. exact (TRANS (@lem4107509) (@lem4107556)). Qed.
Lemma lem4107558 : term248 = True.
Proof. exact (TRANS (@lem4107500) (@lem4107557)). Qed.
Lemma lem4107559 : True = term248.
Proof. exact (SYM (@lem4107558)). Qed.
Lemma lem4107560 : term248.
Proof. exact (EQ_MP (@lem4107559) (@lem0)). Qed.
Lemma lem4107561 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term262 _48286 _48287.
Proof. exact (conj (@lem4107560) (@lem4107422 _48286 _48287 h1)). Qed.
Lemma lem4107563 (x : real) (y : real) : term257 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4107564 (_48286 : int) (_48287 : int) : term263 _48286 _48287.
Proof. exact (@lem4107563 term124 (term231 _48286 _48287)). Qed.
Lemma lem4107565 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term264 _48286 _48287.
Proof. exact (@lem4107564 _48286 _48287 (@lem4107561 _48286 _48287 h1)). Qed.
Lemma lem4107566 (_48286 : int) (_48287 : int) : (term265 _48286 _48287) = (term231 _48286 _48287).
Proof. exact (@lem1982733 (term231 _48286 _48287)). Qed.
Lemma lem4107567 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4107568 (_48286 : int) (_48287 : int) : (term266 _48286 _48287) = (term233 _48286 _48287).
Proof. exact (MK_COMB (@lem4107567) (@lem4107566 _48286 _48287)). Qed.
Lemma lem4107569 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4107570 (_48286 : int) (_48287 : int) : (term264 _48286 _48287) = (term234 _48286 _48287).
Proof. exact (MK_COMB (@lem4107568 _48286 _48287) (@lem4107569)). Qed.
Lemma lem4107571 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term234 _48286 _48287.
Proof. exact (EQ_MP (@lem4107570 _48286 _48287) (@lem4107565 _48286 _48287 h1)). Qed.
Lemma lem4107572 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term267 _48286 _48287.
Proof. exact (conj (@lem4107571 _48286 _48287 h1) (@lem4107497 _48286 _48287 h1)). Qed.
Lemma lem4107574 (x : real) (y : real) : term268 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem4107575 (_48286 : int) (_48287 : int) : term269 _48286 _48287.
Proof. exact (@lem4107574 (term231 _48286 _48287) (term176 _48286 _48287)). Qed.
Lemma lem4107576 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term270 _48286 _48287.
Proof. exact (@lem4107575 _48286 _48287 (@lem4107572 _48286 _48287 h1)). Qed.
Lemma lem4107577 (_48286 : int) (_48287 : int) : (term271 _48286 _48287) = (term272 _48286 _48287).
Proof. exact (@lem1982753 (term201 _48286) (real_of_int _48286) (term273 _48287) (term201 _48287)). Qed.
Lemma lem4107578 (_48286 : int) : (term274 _48286) = (term275 _48286).
Proof. exact (@lem1982713 term153 (real_of_int _48286)). Qed.
Lemma lem4107580 (x : nat) : (real_of_num x) = (term149 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4107581 : term124 = term185.
Proof. exact (@lem4107580 term61). Qed.
Lemma lem4107583 (x : nat) : (term151 x) = (term152 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4107584 : term153 = term154.
Proof. exact (@lem4107583 term61). Qed.
Lemma lem4107585 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4107586 : term276 = term277.
Proof. exact (MK_COMB (@lem4107585) (@lem4107584)). Qed.
Lemma lem4107587 : term278 = term279.
Proof. exact (MK_COMB (@lem4107586) (@lem4107581)). Qed.
Lemma lem4107588 : term280.
Proof. exact (@lem1981473 term153 term124 term124 term124 term111 term124). Qed.
Lemma lem4107590 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107591 : term208 = term209.
Proof. exact (@lem4107590 (NUMERAL 0) term61). Qed.
Lemma lem4107592 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107593 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107594 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107593 h1) (fun h1 : term209 = True => @lem4107592)). Qed.
Lemma lem4107595 : term209 = True.
Proof. exact (EQ_MP (@lem4107594) (@lem4107592)). Qed.
Lemma lem4107596 : term208 = True.
Proof. exact (TRANS (@lem4107591) (@lem4107595)). Qed.
Lemma lem4107597 : True = term208.
Proof. exact (SYM (@lem4107596)). Qed.
Lemma lem4107598 : term208.
Proof. exact (EQ_MP (@lem4107597) (@lem0)). Qed.
Lemma lem4107599 : term281.
Proof. exact (@lem4107588 (@lem4107598)). Qed.
Lemma lem4107601 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107602 : term208 = term209.
Proof. exact (@lem4107601 (NUMERAL 0) term61). Qed.
Lemma lem4107603 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107604 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107605 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107604 h1) (fun h1 : term209 = True => @lem4107603)). Qed.
Lemma lem4107606 : term209 = True.
Proof. exact (EQ_MP (@lem4107605) (@lem4107603)). Qed.
Lemma lem4107607 : term208 = True.
Proof. exact (TRANS (@lem4107602) (@lem4107606)). Qed.
Lemma lem4107608 : True = term208.
Proof. exact (SYM (@lem4107607)). Qed.
Lemma lem4107609 : term208.
Proof. exact (EQ_MP (@lem4107608) (@lem0)). Qed.
Lemma lem4107610 : term282.
Proof. exact (@lem4107599 (@lem4107609)). Qed.
Lemma lem4107612 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107613 : term208 = term209.
Proof. exact (@lem4107612 (NUMERAL 0) term61). Qed.
Lemma lem4107614 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107615 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107616 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107615 h1) (fun h1 : term209 = True => @lem4107614)). Qed.
Lemma lem4107617 : term209 = True.
Proof. exact (EQ_MP (@lem4107616) (@lem4107614)). Qed.
Lemma lem4107618 : term208 = True.
Proof. exact (TRANS (@lem4107613) (@lem4107617)). Qed.
Lemma lem4107619 : True = term208.
Proof. exact (SYM (@lem4107618)). Qed.
Lemma lem4107620 : term208.
Proof. exact (EQ_MP (@lem4107619) (@lem0)). Qed.
Lemma lem4107621 : term283.
Proof. exact (@lem4107610 (@lem4107620)). Qed.
Lemma lem4107623 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4107624 : term162 = term163.
Proof. exact (@lem4107623 term61 term61). Qed.
Lemma lem4107625 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4107626 : term165 = term61.
Proof. exact (EQ_MP (@lem4107625) (@lem940073)). Qed.
Lemma lem4107627 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4107628 : term163 = term124.
Proof. exact (MK_COMB (@lem4107627) (@lem4107626)). Qed.
Lemma lem4107629 : term162 = term124.
Proof. exact (TRANS (@lem4107624) (@lem4107628)). Qed.
Lemma lem4107631 (m : nat) (n : nat) : (term189 m n) = (term190 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4107632 : term186 = term191.
Proof. exact (@lem4107631 term61 term61). Qed.
Lemma lem4107633 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4107634 : term165 = term61.
Proof. exact (EQ_MP (@lem4107633) (@lem940073)). Qed.
Lemma lem4107635 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4107636 : term163 = term124.
Proof. exact (MK_COMB (@lem4107635) (@lem4107634)). Qed.
Lemma lem4107637 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4107638 : term191 = term153.
Proof. exact (MK_COMB (@lem4107637) (@lem4107636)). Qed.
Lemma lem4107639 : term186 = term153.
Proof. exact (TRANS (@lem4107632) (@lem4107638)). Qed.
Lemma lem4107640 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4107641 : term284 = term276.
Proof. exact (MK_COMB (@lem4107640) (@lem4107639)). Qed.
Lemma lem4107642 : term285 = term278.
Proof. exact (MK_COMB (@lem4107641) (@lem4107629)). Qed.
Lemma lem4107644 (m : nat) : (term286 m) = term111.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4107645 : term278 = term111.
Proof. exact (@lem4107644 term61). Qed.
Lemma lem4107646 : term285 = term111.
Proof. exact (TRANS (@lem4107642) (@lem4107645)). Qed.
Lemma lem4107647 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4107648 : term287 = term218.
Proof. exact (MK_COMB (@lem4107647) (@lem4107646)). Qed.
Lemma lem4107649 : term124 = term124.
Proof. exact (eq_refl term124). Qed.
Lemma lem4107650 : term288 = term220.
Proof. exact (MK_COMB (@lem4107648) (@lem4107649)). Qed.
Lemma lem4107652 (x : nat) : (term221 x) = term111.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4107653 : term220 = term111.
Proof. exact (@lem4107652 term61). Qed.
Lemma lem4107654 : term288 = term111.
Proof. exact (TRANS (@lem4107650) (@lem4107653)). Qed.
Lemma lem4107656 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4107657 : term162 = term163.
Proof. exact (@lem4107656 term61 term61). Qed.
Lemma lem4107658 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4107659 : term165 = term61.
Proof. exact (EQ_MP (@lem4107658) (@lem940073)). Qed.
Lemma lem4107660 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4107661 : term163 = term124.
Proof. exact (MK_COMB (@lem4107660) (@lem4107659)). Qed.
Lemma lem4107662 : term162 = term124.
Proof. exact (TRANS (@lem4107657) (@lem4107661)). Qed.
Lemma lem4107663 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem4107664 : term222 = term220.
Proof. exact (MK_COMB (@lem4107663) (@lem4107662)). Qed.
Lemma lem4107666 (x : nat) : (term221 x) = term111.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4107667 : term220 = term111.
Proof. exact (@lem4107666 term61). Qed.
Lemma lem4107668 : term222 = term111.
Proof. exact (TRANS (@lem4107664) (@lem4107667)). Qed.
Lemma lem4107669 : term111 = term222.
Proof. exact (SYM (@lem4107668)). Qed.
Lemma lem4107670 : term288 = term222.
Proof. exact (TRANS (@lem4107654) (@lem4107669)). Qed.
Lemma lem4107671 : term279 = term150.
Proof. exact (@lem4107621 (@lem4107670)). Qed.
Lemma lem4107672 : term278 = term150.
Proof. exact (TRANS (@lem4107587) (@lem4107671)). Qed.
Lemma lem4107674 (x : real) : (term169 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4107675 : term150 = term111.
Proof. exact (@lem4107674 term111). Qed.
Lemma lem4107676 : term278 = term111.
Proof. exact (TRANS (@lem4107672) (@lem4107675)). Qed.
Lemma lem4107677 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4107678 : term289 = term218.
Proof. exact (MK_COMB (@lem4107677) (@lem4107676)). Qed.
Lemma lem4107679 (_48286 : int) : (real_of_int _48286) = (real_of_int _48286).
Proof. exact (eq_refl (real_of_int _48286)). Qed.
Lemma lem4107680 (_48286 : int) : (term275 _48286) = (term290 _48286).
Proof. exact (MK_COMB (@lem4107678) (@lem4107679 _48286)). Qed.
Lemma lem4107681 (_48286 : int) : (term274 _48286) = (term290 _48286).
Proof. exact (TRANS (@lem4107578 _48286) (@lem4107680 _48286)). Qed.
Lemma lem4107682 (_48286 : int) : (term290 _48286) = term111.
Proof. exact (@lem1982719 (real_of_int _48286)). Qed.
Lemma lem4107683 (_48286 : int) : (term274 _48286) = term111.
Proof. exact (TRANS (@lem4107681 _48286) (@lem4107682 _48286)). Qed.
Lemma lem4107684 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4107685 (_48286 : int) : (term291 _48286) = term292.
Proof. exact (MK_COMB (@lem4107684) (@lem4107683 _48286)). Qed.
Lemma lem4107686 (_48287 : int) : (term293 _48287) = (term294 _48287).
Proof. exact (@lem1982759 (real_of_int _48287) (term201 _48287) term153). Qed.
Lemma lem4107687 (_48287 : int) : (term295 _48287) = (term275 _48287).
Proof. exact (@lem1982715 term153 (real_of_int _48287)). Qed.
Lemma lem4107689 (x : nat) : (real_of_num x) = (term149 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4107690 : term124 = term185.
Proof. exact (@lem4107689 term61). Qed.
Lemma lem4107692 (x : nat) : (term151 x) = (term152 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4107693 : term153 = term154.
Proof. exact (@lem4107692 term61). Qed.
Lemma lem4107694 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4107695 : term276 = term277.
Proof. exact (MK_COMB (@lem4107694) (@lem4107693)). Qed.
Lemma lem4107696 : term278 = term279.
Proof. exact (MK_COMB (@lem4107695) (@lem4107690)). Qed.
Lemma lem4107697 : term280.
Proof. exact (@lem1981473 term153 term124 term124 term124 term111 term124). Qed.
Lemma lem4107699 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107700 : term208 = term209.
Proof. exact (@lem4107699 (NUMERAL 0) term61). Qed.
Lemma lem4107701 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107702 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107703 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107702 h1) (fun h1 : term209 = True => @lem4107701)). Qed.
Lemma lem4107704 : term209 = True.
Proof. exact (EQ_MP (@lem4107703) (@lem4107701)). Qed.
Lemma lem4107705 : term208 = True.
Proof. exact (TRANS (@lem4107700) (@lem4107704)). Qed.
Lemma lem4107706 : True = term208.
Proof. exact (SYM (@lem4107705)). Qed.
Lemma lem4107707 : term208.
Proof. exact (EQ_MP (@lem4107706) (@lem0)). Qed.
Lemma lem4107708 : term281.
Proof. exact (@lem4107697 (@lem4107707)). Qed.
Lemma lem4107710 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107711 : term208 = term209.
Proof. exact (@lem4107710 (NUMERAL 0) term61). Qed.
Lemma lem4107712 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107713 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107714 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107713 h1) (fun h1 : term209 = True => @lem4107712)). Qed.
Lemma lem4107715 : term209 = True.
Proof. exact (EQ_MP (@lem4107714) (@lem4107712)). Qed.
Lemma lem4107716 : term208 = True.
Proof. exact (TRANS (@lem4107711) (@lem4107715)). Qed.
Lemma lem4107717 : True = term208.
Proof. exact (SYM (@lem4107716)). Qed.
Lemma lem4107718 : term208.
Proof. exact (EQ_MP (@lem4107717) (@lem0)). Qed.
Lemma lem4107719 : term282.
Proof. exact (@lem4107708 (@lem4107718)). Qed.
Lemma lem4107721 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107722 : term208 = term209.
Proof. exact (@lem4107721 (NUMERAL 0) term61). Qed.
Lemma lem4107723 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107724 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107725 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107724 h1) (fun h1 : term209 = True => @lem4107723)). Qed.
Lemma lem4107726 : term209 = True.
Proof. exact (EQ_MP (@lem4107725) (@lem4107723)). Qed.
Lemma lem4107727 : term208 = True.
Proof. exact (TRANS (@lem4107722) (@lem4107726)). Qed.
Lemma lem4107728 : True = term208.
Proof. exact (SYM (@lem4107727)). Qed.
Lemma lem4107729 : term208.
Proof. exact (EQ_MP (@lem4107728) (@lem0)). Qed.
Lemma lem4107730 : term283.
Proof. exact (@lem4107719 (@lem4107729)). Qed.
Lemma lem4107732 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4107733 : term162 = term163.
Proof. exact (@lem4107732 term61 term61). Qed.
Lemma lem4107734 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4107735 : term165 = term61.
Proof. exact (EQ_MP (@lem4107734) (@lem940073)). Qed.
Lemma lem4107736 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4107737 : term163 = term124.
Proof. exact (MK_COMB (@lem4107736) (@lem4107735)). Qed.
Lemma lem4107738 : term162 = term124.
Proof. exact (TRANS (@lem4107733) (@lem4107737)). Qed.
Lemma lem4107740 (m : nat) (n : nat) : (term189 m n) = (term190 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4107741 : term186 = term191.
Proof. exact (@lem4107740 term61 term61). Qed.
Lemma lem4107742 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4107743 : term165 = term61.
Proof. exact (EQ_MP (@lem4107742) (@lem940073)). Qed.
Lemma lem4107744 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4107745 : term163 = term124.
Proof. exact (MK_COMB (@lem4107744) (@lem4107743)). Qed.
Lemma lem4107746 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4107747 : term191 = term153.
Proof. exact (MK_COMB (@lem4107746) (@lem4107745)). Qed.
Lemma lem4107748 : term186 = term153.
Proof. exact (TRANS (@lem4107741) (@lem4107747)). Qed.
Lemma lem4107749 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4107750 : term284 = term276.
Proof. exact (MK_COMB (@lem4107749) (@lem4107748)). Qed.
Lemma lem4107751 : term285 = term278.
Proof. exact (MK_COMB (@lem4107750) (@lem4107738)). Qed.
Lemma lem4107753 (m : nat) : (term286 m) = term111.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4107754 : term278 = term111.
Proof. exact (@lem4107753 term61). Qed.
Lemma lem4107755 : term285 = term111.
Proof. exact (TRANS (@lem4107751) (@lem4107754)). Qed.
Lemma lem4107756 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4107757 : term287 = term218.
Proof. exact (MK_COMB (@lem4107756) (@lem4107755)). Qed.
Lemma lem4107758 : term124 = term124.
Proof. exact (eq_refl term124). Qed.
Lemma lem4107759 : term288 = term220.
Proof. exact (MK_COMB (@lem4107757) (@lem4107758)). Qed.
Lemma lem4107761 (x : nat) : (term221 x) = term111.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4107762 : term220 = term111.
Proof. exact (@lem4107761 term61). Qed.
Lemma lem4107763 : term288 = term111.
Proof. exact (TRANS (@lem4107759) (@lem4107762)). Qed.
Lemma lem4107765 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4107766 : term162 = term163.
Proof. exact (@lem4107765 term61 term61). Qed.
Lemma lem4107767 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4107768 : term165 = term61.
Proof. exact (EQ_MP (@lem4107767) (@lem940073)). Qed.
Lemma lem4107769 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4107770 : term163 = term124.
Proof. exact (MK_COMB (@lem4107769) (@lem4107768)). Qed.
Lemma lem4107771 : term162 = term124.
Proof. exact (TRANS (@lem4107766) (@lem4107770)). Qed.
Lemma lem4107772 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem4107773 : term222 = term220.
Proof. exact (MK_COMB (@lem4107772) (@lem4107771)). Qed.
Lemma lem4107775 (x : nat) : (term221 x) = term111.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4107776 : term220 = term111.
Proof. exact (@lem4107775 term61). Qed.
Lemma lem4107777 : term222 = term111.
Proof. exact (TRANS (@lem4107773) (@lem4107776)). Qed.
Lemma lem4107778 : term111 = term222.
Proof. exact (SYM (@lem4107777)). Qed.
Lemma lem4107779 : term288 = term222.
Proof. exact (TRANS (@lem4107763) (@lem4107778)). Qed.
Lemma lem4107780 : term279 = term150.
Proof. exact (@lem4107730 (@lem4107779)). Qed.
Lemma lem4107781 : term278 = term150.
Proof. exact (TRANS (@lem4107696) (@lem4107780)). Qed.
Lemma lem4107783 (x : real) : (term169 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4107784 : term150 = term111.
Proof. exact (@lem4107783 term111). Qed.
Lemma lem4107785 : term278 = term111.
Proof. exact (TRANS (@lem4107781) (@lem4107784)). Qed.
Lemma lem4107786 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4107787 : term289 = term218.
Proof. exact (MK_COMB (@lem4107786) (@lem4107785)). Qed.
Lemma lem4107788 (_48287 : int) : (real_of_int _48287) = (real_of_int _48287).
Proof. exact (eq_refl (real_of_int _48287)). Qed.
Lemma lem4107789 (_48287 : int) : (term275 _48287) = (term290 _48287).
Proof. exact (MK_COMB (@lem4107787) (@lem4107788 _48287)). Qed.
Lemma lem4107790 (_48287 : int) : (term295 _48287) = (term290 _48287).
Proof. exact (TRANS (@lem4107687 _48287) (@lem4107789 _48287)). Qed.
Lemma lem4107791 (_48287 : int) : (term290 _48287) = term111.
Proof. exact (@lem1982719 (real_of_int _48287)). Qed.
Lemma lem4107792 (_48287 : int) : (term295 _48287) = term111.
Proof. exact (TRANS (@lem4107790 _48287) (@lem4107791 _48287)). Qed.
Lemma lem4107793 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4107794 (_48287 : int) : (term296 _48287) = term292.
Proof. exact (MK_COMB (@lem4107793) (@lem4107792 _48287)). Qed.
Lemma lem4107795 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem4107796 (_48287 : int) : (term294 _48287) = term297.
Proof. exact (MK_COMB (@lem4107794 _48287) (@lem4107795)). Qed.
Lemma lem4107797 (_48287 : int) : (term293 _48287) = term297.
Proof. exact (TRANS (@lem4107686 _48287) (@lem4107796 _48287)). Qed.
Lemma lem4107798 : term297 = term153.
Proof. exact (@lem1982721 term153). Qed.
Lemma lem4107799 (_48287 : int) : (term293 _48287) = term153.
Proof. exact (TRANS (@lem4107797 _48287) (@lem4107798)). Qed.
Lemma lem4107800 (_48286 : int) (_48287 : int) : (term272 _48286 _48287) = term297.
Proof. exact (MK_COMB (@lem4107685 _48286) (@lem4107799 _48287)). Qed.
Lemma lem4107801 (_48286 : int) (_48287 : int) : (term271 _48286 _48287) = term297.
Proof. exact (TRANS (@lem4107577 _48286 _48287) (@lem4107800 _48286 _48287)). Qed.
Lemma lem4107802 : term297 = term153.
Proof. exact (@lem1982721 term153). Qed.
Lemma lem4107803 (_48286 : int) (_48287 : int) : (term271 _48286 _48287) = term153.
Proof. exact (TRANS (@lem4107801 _48286 _48287) (@lem4107802)). Qed.
Lemma lem4107804 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4107805 (_48286 : int) (_48287 : int) : (term298 _48286 _48287) = term299.
Proof. exact (MK_COMB (@lem4107804) (@lem4107803 _48286 _48287)). Qed.
Lemma lem4107806 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4107807 (_48286 : int) (_48287 : int) : (term270 _48286 _48287) = term300.
Proof. exact (MK_COMB (@lem4107805 _48286 _48287) (@lem4107806)). Qed.
Lemma lem4107808 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : term300.
Proof. exact (EQ_MP (@lem4107807 _48286 _48287) (@lem4107576 _48286 _48287 h1)). Qed.
Lemma lem4107810 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4107811 : term300 = term301.
Proof. exact (@lem4107810 term111 term153). Qed.
Lemma lem4107813 (x : nat) : (term151 x) = (term152 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4107814 : term153 = term154.
Proof. exact (@lem4107813 term61). Qed.
Lemma lem4107816 (x : nat) : (real_of_num x) = (term149 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4107817 : term111 = term150.
Proof. exact (@lem4107816 (NUMERAL 0)). Qed.
Lemma lem4107818 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4107819 : term113 = term302.
Proof. exact (MK_COMB (@lem4107818) (@lem4107817)). Qed.
Lemma lem4107820 : term301 = term303.
Proof. exact (MK_COMB (@lem4107819) (@lem4107814)). Qed.
Lemma lem4107821 : term304.
Proof. exact (@lem1980026 term111 term124 term153 term124). Qed.
Lemma lem4107823 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107824 : term208 = term209.
Proof. exact (@lem4107823 (NUMERAL 0) term61). Qed.
Lemma lem4107825 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107826 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107827 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107826 h1) (fun h1 : term209 = True => @lem4107825)). Qed.
Lemma lem4107828 : term209 = True.
Proof. exact (EQ_MP (@lem4107827) (@lem4107825)). Qed.
Lemma lem4107829 : term208 = True.
Proof. exact (TRANS (@lem4107824) (@lem4107828)). Qed.
Lemma lem4107830 : True = term208.
Proof. exact (SYM (@lem4107829)). Qed.
Lemma lem4107831 : term208.
Proof. exact (EQ_MP (@lem4107830) (@lem0)). Qed.
Lemma lem4107832 : term305.
Proof. exact (@lem4107821 (@lem4107831)). Qed.
Lemma lem4107834 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4107835 : term208 = term209.
Proof. exact (@lem4107834 (NUMERAL 0) term61). Qed.
Lemma lem4107836 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107837 (h1 : term210 = (BIT1 0)) : term209 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4107838 : (term210 = (BIT1 0)) = (term209 = True).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107837 h1) (fun h1 : term209 = True => @lem4107836)). Qed.
Lemma lem4107839 : term209 = True.
Proof. exact (EQ_MP (@lem4107838) (@lem4107836)). Qed.
Lemma lem4107840 : term208 = True.
Proof. exact (TRANS (@lem4107835) (@lem4107839)). Qed.
Lemma lem4107841 : True = term208.
Proof. exact (SYM (@lem4107840)). Qed.
Lemma lem4107842 : term208.
Proof. exact (EQ_MP (@lem4107841) (@lem0)). Qed.
Lemma lem4107843 : term303 = term306.
Proof. exact (@lem4107832 (@lem4107842)). Qed.
Lemma lem4107845 (m : nat) (n : nat) : (term189 m n) = (term190 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4107846 : term186 = term191.
Proof. exact (@lem4107845 term61 term61). Qed.
Lemma lem4107847 : (term164 = (BIT1 0)) = (term165 = term61).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4107848 : term165 = term61.
Proof. exact (EQ_MP (@lem4107847) (@lem940073)). Qed.
Lemma lem4107849 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4107850 : term163 = term124.
Proof. exact (MK_COMB (@lem4107849) (@lem4107848)). Qed.
Lemma lem4107851 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4107852 : term191 = term153.
Proof. exact (MK_COMB (@lem4107851) (@lem4107850)). Qed.
Lemma lem4107853 : term186 = term153.
Proof. exact (TRANS (@lem4107846) (@lem4107852)). Qed.
Lemma lem4107855 (x : nat) : (term221 x) = term111.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4107856 : term220 = term111.
Proof. exact (@lem4107855 term61). Qed.
Lemma lem4107857 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4107858 : term307 = term113.
Proof. exact (MK_COMB (@lem4107857) (@lem4107856)). Qed.
Lemma lem4107859 : term306 = term301.
Proof. exact (MK_COMB (@lem4107858) (@lem4107853)). Qed.
Lemma lem4107861 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4107862 : term301 = term310.
Proof. exact (@lem4107861 (NUMERAL 0) term61). Qed.
Lemma lem4107863 : term210 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4107864 (h1 : term210 = (BIT1 0)) : (term61 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem4107865 : (term210 = (BIT1 0)) = ((term61 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term210 = (BIT1 0) => @lem4107864 h1) (fun h1 : (term61 = (NUMERAL 0)) = False => @lem4107863)). Qed.
Lemma lem4107866 : (term61 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4107865) (@lem4107863)). Qed.
Lemma lem4107867 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4107868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4107869 : term311 = (and True).
Proof. exact (MK_COMB (@lem4107868) (@lem4107867)). Qed.
Lemma lem4107870 : term310 = (True /\ False).
Proof. exact (MK_COMB (@lem4107869) (@lem4107866)). Qed.
Lemma lem4107872 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4107873 : term310 = False.
Proof. exact (TRANS (@lem4107870) (@lem4107872)). Qed.
Lemma lem4107874 : term301 = False.
Proof. exact (TRANS (@lem4107862) (@lem4107873)). Qed.
Lemma lem4107875 : term306 = False.
Proof. exact (TRANS (@lem4107859) (@lem4107874)). Qed.
Lemma lem4107876 : term303 = False.
Proof. exact (TRANS (@lem4107843) (@lem4107875)). Qed.
Lemma lem4107877 : term301 = False.
Proof. exact (TRANS (@lem4107820) (@lem4107876)). Qed.
Lemma lem4107878 : term300 = False.
Proof. exact (TRANS (@lem4107811) (@lem4107877)). Qed.
Lemma lem4107879 (_48286 : int) (_48287 : int) (h1 : term247 _48286 _48287) : False.
Proof. exact (EQ_MP (@lem4107878) (@lem4107808 _48286 _48287 h1)). Qed.
Lemma lem4107880 (_48286 : int) (_48287 : int) (h1 : term245 _48286 _48287) : False.
Proof. exact (or_elim (@lem4106953 _48286 _48287 h1) (fun h0 : term247 _48286 _48287 => @lem4107416 _48286 _48287 h0) (fun h0 : term247 _48286 _48287 => @lem4107879 _48286 _48287 h0)). Qed.
Lemma lem4107882 (_48286 : int) (_48287 : int) (h1 : term245 _48286 _48287) : term245 _48286 _48287.
Proof. exact (h1). Qed.
Lemma lem4107883 (_48286 : int) (_48287 : int) (h1 : term245 _48286 _48287) : (term245 _48286 _48287) = False.
Proof. exact (prop_ext (fun h2 : term245 _48286 _48287 => @lem4107880 _48286 _48287 h1) (fun h2 : False => @lem4107882 _48286 _48287 h1)). Qed.
Lemma lem4107884 (_48286 : int) (_48287 : int) (h1 : term245 _48286 _48287) : False.
Proof. exact (EQ_MP (@lem4107883 _48286 _48287 h1) (@lem4107882 _48286 _48287 h1)). Qed.
Lemma lem4107885 (_48286 : int) (_48287 : int) (h1 : term142 _48286 _48287) : term142 _48286 _48287.
Proof. exact (h1). Qed.
Lemma lem4107886 (_48286 : int) (_48287 : int) (h1 : term142 _48286 _48287) : term245 _48286 _48287.
Proof. exact (EQ_MP (@lem4106943 _48286 _48287) (@lem4107885 _48286 _48287 h1)). Qed.
Lemma lem4107887 (_48286 : int) (_48287 : int) (h1 : term142 _48286 _48287) : (term245 _48286 _48287) = False.
Proof. exact (prop_ext (fun h2 : term245 _48286 _48287 => @lem4107884 _48286 _48287 h2) (fun h2 : False => @lem4107886 _48286 _48287 h1)). Qed.
Lemma lem4107888 (_48286 : int) (_48287 : int) (h1 : term142 _48286 _48287) : False.
Proof. exact (EQ_MP (@lem4107887 _48286 _48287 h1) (@lem4107886 _48286 _48287 h1)). Qed.
Lemma lem4107889 (_48286 : int) (_48287 : int) : term312 _48286 _48287.
Proof. exact (fun h0 : term142 _48286 _48287 => @lem4107888 _48286 _48287 h0). Qed.
Lemma lem4107890 (_48286 : int) (_48287 : int) : term313 _48286 _48287.
Proof. exact (@lem1386578 (term314 _48286 _48287)). Qed.
Lemma lem4107893 (_48286 : int) (_48287 : int) : term314 _48286 _48287.
Proof. exact (@lem4107890 _48286 _48287 (@lem4107889 _48286 _48287)). Qed.
Lemma lem4107894 (_48286 : int) (_48287 : int) : (term140 _48286 _48287) = (term104 _48286 _48287).
Proof. exact (SYM (@lem4106450 _48286 _48287)). Qed.
Lemma lem4107895 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4107896 (_48286 : int) (_48287 : int) : (term314 _48286 _48287) = (term73 _48286 _48287).
Proof. exact (MK_COMB (@lem4107895) (@lem4107894 _48286 _48287)). Qed.
Lemma lem4107897 (_48286 : int) (_48287 : int) : term73 _48286 _48287.
Proof. exact (EQ_MP (@lem4107896 _48286 _48287) (@lem4107893 _48286 _48287)). Qed.
Lemma lem4107898 (_48286 : int) (_48287 : int) : term74 _48286 _48287.
Proof. exact (EQ_MP (@lem4106257 _48286 _48287) (@lem4107897 _48286 _48287)). Qed.
Lemma lem4107899 (n : nat) (x : nat) : term315 n x.
Proof. exact (@lem4107898 (int_of_num n) (int_of_num x)). Qed.
Lemma lem4107900 (n : nat) (x : nat) : term316 n x.
Proof. exact (@lem4107899 n x (@lem4106253 n)). Qed.
Lemma lem4107901 (n : nat) (x : nat) : term70 n x.
Proof. exact (@lem4107900 n x (@lem4106256 x)). Qed.
Lemma lem4107902 (n : nat) (x : nat) : (term70 n x) = ((term40 x n) = (term41 n x)).
Proof. exact (SYM (@lem4106250 n x)). Qed.
Lemma lem4107912 (p : Prop) : term317 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem4107913 (p : Prop) : (term317 p) = (term318 p).
Proof. exact (eq_refl (term317 p)). Qed.
Lemma lem4107914 (p : Prop) : term318 p.
Proof. exact (EQ_MP (@lem4107913 p) (@lem4107912 p)). Qed.
Lemma lem4107915 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem4107916 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem4107925 (q : Prop) : (term319 q) = (term319 q).
Proof. exact (eq_refl (term319 q)). Qed.
Lemma lem4107926 (q : Prop) (p : Prop) (h1 : p = True) : (term320 q p) = (term321 q).
Proof. exact (MK_COMB (@lem4107925 q) (@lem4107915 p h1)). Qed.
Lemma lem4107927 (q : Prop) : (term321 q) = ((term322 q) = (term323 q)).
Proof. exact (eq_refl (term321 q)). Qed.
Lemma lem4107928 (q : Prop) (p : Prop) : (term324 q p) = (term324 q p).
Proof. exact (eq_refl (term324 q p)). Qed.
Lemma lem4107929 (p : Prop) (q : Prop) : ((term320 q p) = (term321 q)) = ((term320 q p) = ((term322 q) = (term323 q))).
Proof. exact (MK_COMB (@lem4107928 q p) (@lem4107927 q)). Qed.
Lemma lem4107930 (p : Prop) (q : Prop) : (term320 q p) = ((term325 p q) = (term326 p q)).
Proof. exact (eq_refl (term320 q p)). Qed.
Lemma lem4107931 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4107932 (p : Prop) (q : Prop) : (term324 q p) = (term327 p q).
Proof. exact (MK_COMB (@lem4107931) (@lem4107930 p q)). Qed.
Lemma lem4107933 (q : Prop) : ((term322 q) = (term323 q)) = ((term322 q) = (term323 q)).
Proof. exact (eq_refl ((term322 q) = (term323 q))). Qed.
Lemma lem4107934 (p : Prop) (q : Prop) : ((term320 q p) = ((term322 q) = (term323 q))) = (((term325 p q) = (term326 p q)) = ((term322 q) = (term323 q))).
Proof. exact (MK_COMB (@lem4107932 p q) (@lem4107933 q)). Qed.
Lemma lem4107935 (p : Prop) (q : Prop) : ((term320 q p) = (term321 q)) = (((term325 p q) = (term326 p q)) = ((term322 q) = (term323 q))).
Proof. exact (TRANS (@lem4107929 p q) (@lem4107934 p q)). Qed.
Lemma lem4107936 (q : Prop) (p : Prop) (h1 : p = True) : ((term325 p q) = (term326 p q)) = ((term322 q) = (term323 q)).
Proof. exact (EQ_MP (@lem4107935 p q) (@lem4107926 q p h1)). Qed.
Lemma lem4107937 (q : Prop) (p : Prop) (h1 : p = True) : ((term322 q) = (term323 q)) = ((term325 p q) = (term326 p q)).
Proof. exact (SYM (@lem4107936 q p h1)). Qed.
Lemma lem4107938 (q : Prop) : (term319 q) = (term319 q).
Proof. exact (eq_refl (term319 q)). Qed.
Lemma lem4107939 (q : Prop) (p : Prop) (h1 : p = False) : (term320 q p) = (term328 q).
Proof. exact (MK_COMB (@lem4107938 q) (@lem4107916 p h1)). Qed.
Lemma lem4107940 (q : Prop) : (term328 q) = ((term329 q) = (term330 q)).
Proof. exact (eq_refl (term328 q)). Qed.
Lemma lem4107941 (q : Prop) (p : Prop) : (term324 q p) = (term324 q p).
Proof. exact (eq_refl (term324 q p)). Qed.
Lemma lem4107942 (p : Prop) (q : Prop) : ((term320 q p) = (term328 q)) = ((term320 q p) = ((term329 q) = (term330 q))).
Proof. exact (MK_COMB (@lem4107941 q p) (@lem4107940 q)). Qed.
Lemma lem4107943 (p : Prop) (q : Prop) : (term320 q p) = ((term325 p q) = (term326 p q)).
Proof. exact (eq_refl (term320 q p)). Qed.
Lemma lem4107944 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4107945 (p : Prop) (q : Prop) : (term324 q p) = (term327 p q).
Proof. exact (MK_COMB (@lem4107944) (@lem4107943 p q)). Qed.
Lemma lem4107946 (q : Prop) : ((term329 q) = (term330 q)) = ((term329 q) = (term330 q)).
Proof. exact (eq_refl ((term329 q) = (term330 q))). Qed.
Lemma lem4107947 (p : Prop) (q : Prop) : ((term320 q p) = ((term329 q) = (term330 q))) = (((term325 p q) = (term326 p q)) = ((term329 q) = (term330 q))).
Proof. exact (MK_COMB (@lem4107945 p q) (@lem4107946 q)). Qed.
Lemma lem4107948 (p : Prop) (q : Prop) : ((term320 q p) = (term328 q)) = (((term325 p q) = (term326 p q)) = ((term329 q) = (term330 q))).
Proof. exact (TRANS (@lem4107942 p q) (@lem4107947 p q)). Qed.
Lemma lem4107949 (q : Prop) (p : Prop) (h1 : p = False) : ((term325 p q) = (term326 p q)) = ((term329 q) = (term330 q)).
Proof. exact (EQ_MP (@lem4107948 p q) (@lem4107939 q p h1)). Qed.
Lemma lem4107950 (q : Prop) (p : Prop) (h1 : p = False) : ((term329 q) = (term330 q)) = ((term325 p q) = (term326 p q)).
Proof. exact (SYM (@lem4107949 q p h1)). Qed.
Lemma lem4107954 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4107955 (q : Prop) : (True /\ q) = q.
Proof. exact (@lem4107954 q). Qed.
Lemma lem4107956 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4107957 (q : Prop) : (term322 q) = (~ q).
Proof. exact (MK_COMB (@lem4107956) (@lem4107955 q)). Qed.
Lemma lem4107958 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4107959 (q : Prop) : (term331 q) = (term332 q).
Proof. exact (MK_COMB (@lem4107958) (@lem4107957 q)). Qed.
Lemma lem4107961 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4107962 (q : Prop) : (term323 q) = (~ q).
Proof. exact (@lem4107961 (~ q)). Qed.
Lemma lem4107963 (q : Prop) : ((term322 q) = (term323 q)) = ((~ q) = (~ q)).
Proof. exact (MK_COMB (@lem4107959 q) (@lem4107962 q)). Qed.
Lemma lem4107965 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4107966 (x : Prop) : (x = x) = True.
Proof. exact (@lem4107965 Prop x). Qed.
Lemma lem4107967 (q : Prop) : ((~ q) = (~ q)) = True.
Proof. exact (@lem4107966 (~ q)). Qed.
Lemma lem4107968 (q : Prop) : ((term322 q) = (term323 q)) = True.
Proof. exact (TRANS (@lem4107963 q) (@lem4107967 q)). Qed.
Lemma lem4107969 (q : Prop) : True = ((term322 q) = (term323 q)).
Proof. exact (SYM (@lem4107968 q)). Qed.
Lemma lem4107970 (q : Prop) : (term322 q) = (term323 q).
Proof. exact (EQ_MP (@lem4107969 q) (@lem0)). Qed.
Lemma lem4107974 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4107975 (q : Prop) : (False /\ q) = False.
Proof. exact (@lem4107974 q). Qed.
Lemma lem4107976 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4107977 (q : Prop) : (term329 q) = (~ False).
Proof. exact (MK_COMB (@lem4107976) (@lem4107975 q)). Qed.
Lemma lem4107979 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4107980 (q : Prop) : (term329 q) = True.
Proof. exact (TRANS (@lem4107977 q) (@lem4107979)). Qed.
Lemma lem4107981 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4107982 (q : Prop) : (term333 q) = (@eq Prop True).
Proof. exact (MK_COMB (@lem4107981) (@lem4107980 q)). Qed.
Lemma lem4107984 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4107985 (q : Prop) : (term330 q) = True.
Proof. exact (@lem4107984 (~ q)). Qed.
Lemma lem4107986 (q : Prop) : ((term329 q) = (term330 q)) = (True = True).
Proof. exact (MK_COMB (@lem4107982 q) (@lem4107985 q)). Qed.
Lemma lem4107988 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem4107989 : (True = True) = True.
Proof. exact (@lem4107988 True). Qed.
Lemma lem4107990 (q : Prop) : ((term329 q) = (term330 q)) = True.
Proof. exact (TRANS (@lem4107986 q) (@lem4107989)). Qed.
Lemma lem4107991 (q : Prop) : True = ((term329 q) = (term330 q)).
Proof. exact (SYM (@lem4107990 q)). Qed.
Lemma lem4107992 (q : Prop) : (term329 q) = (term330 q).
Proof. exact (EQ_MP (@lem4107991 q) (@lem0)). Qed.
Lemma lem4107993 (q : Prop) (p : Prop) (h1 : p = False) : (term325 p q) = (term326 p q).
Proof. exact (EQ_MP (@lem4107950 q p h1) (@lem4107992 q)). Qed.
Lemma lem4107994 (q : Prop) (p : Prop) (h1 : p = True) : (term325 p q) = (term326 p q).
Proof. exact (EQ_MP (@lem4107937 q p h1) (@lem4107970 q)). Qed.
Lemma lem4107998 (t1 : Prop) : term334 t1.
Proof. exact (@lem10299 t1). Qed.
Lemma lem4107999 (t1 : Prop) : (term334 t1) = (term335 t1).
Proof. exact (eq_refl (term334 t1)). Qed.
Lemma lem4108000 (t1 : Prop) : term335 t1.
Proof. exact (EQ_MP (@lem4107999 t1) (@lem4107998 t1)). Qed.
Lemma lem4108001 (t1 : Prop) (t2 : Prop) : term336 t1 t2.
Proof. exact (@lem4108000 t1 t2). Qed.
Lemma lem4108002 (t1 : Prop) (t2 : Prop) : (term336 t1 t2) = ((term337 t1 t2) = (term338 t1 t2)).
Proof. exact (eq_refl (term336 t1 t2)). Qed.
Lemma lem4108004 {A : Type'} (P : A -> Prop) : term339 A P.
Proof. exact (@lem10884 A P). Qed.
Lemma lem4108005 {A : Type'} (P : A -> Prop) : (term339 A P) = ((term340 A P) = (term341 A P)).
Proof. exact (eq_refl (term339 A P)). Qed.
Lemma lem4108009 (t2 : Prop) (t1 : Prop) (h1 : (term342 t1 t2) = (t2 -> t1)) : (term342 t1 t2) = (t2 -> t1).
Proof. exact (h1). Qed.
Lemma lem4108010 (t2 : Prop) (t1 : Prop) (h1 : (term342 t1 t2) = (t2 -> t1)) : (t2 -> t1) = (term342 t1 t2).
Proof. exact (SYM (@lem4108009 t2 t1 h1)). Qed.
Lemma lem4108011 (t1 : Prop) (t2 : Prop) (h1 : (t2 -> t1) = (term342 t1 t2)) : (t2 -> t1) = (term342 t1 t2).
Proof. exact (h1). Qed.
Lemma lem4108012 (t1 : Prop) (t2 : Prop) (h1 : (t2 -> t1) = (term342 t1 t2)) : (term342 t1 t2) = (t2 -> t1).
Proof. exact (SYM (@lem4108011 t1 t2 h1)). Qed.
Lemma lem4108013 (t1 : Prop) (t2 : Prop) : ((term342 t1 t2) = (t2 -> t1)) = ((t2 -> t1) = (term342 t1 t2)).
Proof. exact (prop_ext (fun h1 : (term342 t1 t2) = (t2 -> t1) => @lem4108010 t2 t1 h1) (fun h1 : (t2 -> t1) = (term342 t1 t2) => @lem4108012 t1 t2 h1)). Qed.
Lemma lem4108014 (t1 : Prop) : (term343 t1) = (term344 t1).
Proof. exact (fun_ext (fun t2 : Prop => @lem4108013 t1 t2)). Qed.
Lemma lem4108015 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem4108016 (t1 : Prop) : (term345 t1) = (term346 t1).
Proof. exact (MK_COMB (@lem4108015) (@lem4108014 t1)). Qed.
Lemma lem4108017 : term347 = term348.
Proof. exact (fun_ext (fun t1 : Prop => @lem4108016 t1)). Qed.
Lemma lem4108018 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem4108019 : term349 = term350.
Proof. exact (MK_COMB (@lem4108018) (@lem4108017)). Qed.
Lemma lem4108020 : term350.
Proof. exact (EQ_MP (@lem4108019) (@lem10414)). Qed.
Lemma lem4108021 (t1 : Prop) : term351 t1.
Proof. exact (@lem4108020 t1). Qed.
Lemma lem4108022 (t1 : Prop) : (term351 t1) = (term346 t1).
Proof. exact (eq_refl (term351 t1)). Qed.
Lemma lem4108023 (t1 : Prop) : term346 t1.
Proof. exact (EQ_MP (@lem4108022 t1) (@lem4108021 t1)). Qed.
Lemma lem4108024 (t1 : Prop) (t2 : Prop) : term352 t1 t2.
Proof. exact (@lem4108023 t1 t2). Qed.
Lemma lem4108025 (t1 : Prop) (t2 : Prop) : (term352 t1 t2) = ((t2 -> t1) = (term342 t1 t2)).
Proof. exact (eq_refl (term352 t1 t2)). Qed.
Lemma lem4108027 {A : Type'} (f : type686 A) : term353 A f.
Proof. exact (@lem9784 (f = (@EMPTY (A -> Prop)))). Qed.
Lemma lem4108028 {A : Type'} (f : type686 A) : (term353 A f) = (term354 A f).
Proof. exact (eq_refl (term353 A f)). Qed.
Lemma lem4108029 {A : Type'} (f : type686 A) : term354 A f.
Proof. exact (EQ_MP (@lem4108028 A f) (@lem4108027 A f)). Qed.
Lemma lem4108031 {A : Type'} (f : type686 A) (h1 : term355 A f) : term355 A f.
Proof. exact (h1). Qed.
Lemma lem4108032 (n : nat) : term356 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem4108033 (n : nat) : (term356 n) = (term357 n).
Proof. exact (eq_refl (term356 n)). Qed.
Lemma lem4108034 (n : nat) : term357 n.
Proof. exact (EQ_MP (@lem4108033 n) (@lem4108032 n)). Qed.
Lemma lem4108035 (n : nat) : (term357 n) = ((term357 n) = True).
Proof. exact (@lem7 (term357 n)). Qed.
Lemma lem4108047 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = ((@FINITE _92140 (@EMPTY _92140)) = True).
Proof. exact (@lem7 (@FINITE _92140 (@EMPTY _92140))). Qed.
Lemma lem4108066 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem4108067 {A : Type'} (t : A -> Prop) : (@IN (A -> Prop) t) = (@IN (A -> Prop) t).
Proof. exact (eq_refl (@IN (A -> Prop) t)). Qed.
Lemma lem4108068 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@IN (A -> Prop) t f) = (@IN (A -> Prop) t (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem4108067 A t) (@lem4108066 A f h1)). Qed.
Lemma lem4108069 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4108070 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term358 A t f) = (term359 A t).
Proof. exact (MK_COMB (@lem4108069) (@lem4108068 A t f h1)). Qed.
Lemma lem4108072 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem4108073 {A : Type'} (u : A -> Prop) : (@IN (A -> Prop) u) = (@IN (A -> Prop) u).
Proof. exact (eq_refl (@IN (A -> Prop) u)). Qed.
Lemma lem4108074 {A : Type'} (u : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@IN (A -> Prop) u f) = (@IN (A -> Prop) u (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem4108073 A u) (@lem4108072 A f h1)). Qed.
Lemma lem4108075 {A : Type'} (t : A -> Prop) (u : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term360 A t u f) = (term361 A t u).
Proof. exact (MK_COMB (@lem4108070 A t f h1) (@lem4108074 A u f h1)). Qed.
Lemma lem4108078 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4108079 {A : Type'} (t : A -> Prop) (u : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term362 A t u f) = (term363 A t u).
Proof. exact (MK_COMB (@lem4108078) (@lem4108075 A t u f h1)). Qed.
Lemma lem4108082 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term364 A u t) = (term364 A u t).
Proof. exact (eq_refl (term364 A u t)). Qed.
Lemma lem4108083 {A : Type'} (u : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term365 A f u t) = (term366 A u t).
Proof. exact (MK_COMB (@lem4108079 A t u f h1) (@lem4108082 A u t)). Qed.
Lemma lem4108086 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term367 A f t) = (term368 A t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4108083 A u t f h1)). Qed.
Lemma lem4108087 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4108088 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term369 A f t) = (term370 A t).
Proof. exact (MK_COMB (@lem4108087 A) (@lem4108086 A t f h1)). Qed.
Lemma lem4108093 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term371 A f) = (term372 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4108088 A t f h1)). Qed.
Lemma lem4108094 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4108095 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term373 A f) = (term374 A).
Proof. exact (MK_COMB (@lem4108094 A) (@lem4108093 A f h1)). Qed.
Lemma lem4108100 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4108101 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term375 A f) = (term376 A).
Proof. exact (MK_COMB (@lem4108100) (@lem4108095 A f h1)). Qed.
Lemma lem4108109 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem4108110 {A : Type'} (t : A -> Prop) : (@IN (A -> Prop) t) = (@IN (A -> Prop) t).
Proof. exact (eq_refl (@IN (A -> Prop) t)). Qed.
Lemma lem4108111 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@IN (A -> Prop) t f) = (@IN (A -> Prop) t (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem4108110 A t) (@lem4108109 A f h1)). Qed.
Lemma lem4108112 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4108113 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term377 A t f) = (term378 A t).
Proof. exact (MK_COMB (@lem4108112) (@lem4108111 A t f h1)). Qed.
Lemma lem4108116 {A : Type'} (t : A -> Prop) (n : nat) : (term379 A t n) = (term379 A t n).
Proof. exact (eq_refl (term379 A t n)). Qed.
Lemma lem4108117 {A : Type'} (t : A -> Prop) (n : nat) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term380 A f t n) = (term381 A t n).
Proof. exact (MK_COMB (@lem4108113 A t f h1) (@lem4108116 A t n)). Qed.
Lemma lem4108120 {A : Type'} (n : nat) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term382 A f n) = (term383 A n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4108117 A t n f h1)). Qed.
Lemma lem4108121 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4108122 {A : Type'} (n : nat) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term384 A f n) = (term385 A n).
Proof. exact (MK_COMB (@lem4108121 A) (@lem4108120 A n f h1)). Qed.
Lemma lem4108127 {A : Type'} (n : nat) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term386 A f n) = (term387 A n).
Proof. exact (MK_COMB (@lem4108101 A f h1) (@lem4108122 A n f h1)). Qed.
Lemma lem4108130 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4108131 {A : Type'} (n : nat) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term388 A f n) = (term389 A n).
Proof. exact (MK_COMB (@lem4108130) (@lem4108127 A n f h1)). Qed.
Lemma lem4108135 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem4108136 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem4108137 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@UNIONS A f) = (@UNIONS A (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem4108136 A) (@lem4108135 A f h1)). Qed.
Lemma lem4108139 {_86801 : Type'} : (@UNIONS _86801 (@EMPTY (_86801 -> Prop))) = (@EMPTY _86801).
Proof. exact (EQ_MP (@lem3322101 _86801) (@lem3322164 _86801)). Qed.
Lemma lem4108140 {A : Type'} : (@UNIONS A (@EMPTY (A -> Prop))) = (@EMPTY A).
Proof. exact (@lem4108139 A). Qed.
Lemma lem4108141 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@UNIONS A f) = (@EMPTY A).
Proof. exact (TRANS (@lem4108137 A f h1) (@lem4108140 A)). Qed.
Lemma lem4108142 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem4108143 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term390 A f) = (@FINITE A (@EMPTY A)).
Proof. exact (MK_COMB (@lem4108142 A) (@lem4108141 A f h1)). Qed.
Lemma lem4108145 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem4108047 _92140) (@lem3596285 _92140)). Qed.
Lemma lem4108146 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (@lem4108145 A). Qed.
Lemma lem4108147 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term390 A f) = True.
Proof. exact (TRANS (@lem4108143 A f h1) (@lem4108146 A)). Qed.
Lemma lem4108148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4108149 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term391 A f) = (and True).
Proof. exact (MK_COMB (@lem4108148) (@lem4108147 A f h1)). Qed.
Lemma lem4108151 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem4108152 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem4108153 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@UNIONS A f) = (@UNIONS A (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem4108152 A) (@lem4108151 A f h1)). Qed.
Lemma lem4108155 {_86801 : Type'} : (@UNIONS _86801 (@EMPTY (_86801 -> Prop))) = (@EMPTY _86801).
Proof. exact (EQ_MP (@lem3322101 _86801) (@lem3322164 _86801)). Qed.
Lemma lem4108156 {A : Type'} : (@UNIONS A (@EMPTY (A -> Prop))) = (@EMPTY A).
Proof. exact (@lem4108155 A). Qed.
Lemma lem4108157 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@UNIONS A f) = (@EMPTY A).
Proof. exact (TRANS (@lem4108153 A f h1) (@lem4108156 A)). Qed.
Lemma lem4108158 {A : Type'} : (@CARD A) = (@CARD A).
Proof. exact (eq_refl (@CARD A)). Qed.
Lemma lem4108159 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term392 A f) = (@CARD A (@EMPTY A)).
Proof. exact (MK_COMB (@lem4108158 A) (@lem4108157 A f h1)). Qed.
Lemma lem4108161 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem4108162 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term392 A f) = (NUMERAL 0).
Proof. exact (TRANS (@lem4108159 A f h1) (@lem4108161 A)). Qed.
Lemma lem4108163 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4108164 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term393 A f) = term394.
Proof. exact (MK_COMB (@lem4108163) (@lem4108162 A f h1)). Qed.
Lemma lem4108165 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4108166 {A : Type'} (n : nat) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term395 A f n) = (term357 n).
Proof. exact (MK_COMB (@lem4108164 A f h1) (@lem4108165 n)). Qed.
Lemma lem4108168 (n : nat) : (term357 n) = True.
Proof. exact (EQ_MP (@lem4108035 n) (@lem4108034 n)). Qed.
Lemma lem4108169 {A : Type'} (n : nat) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term395 A f n) = True.
Proof. exact (TRANS (@lem4108166 A n f h1) (@lem4108168 n)). Qed.
Lemma lem4108170 {A : Type'} (n : nat) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term396 A f n) = (True /\ True).
Proof. exact (MK_COMB (@lem4108149 A f h1) (@lem4108169 A n f h1)). Qed.
Lemma lem4108172 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4108173 : (True /\ True) = True.
Proof. exact (@lem4108172 True). Qed.
Lemma lem4108174 {A : Type'} (n : nat) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term396 A f n) = True.
Proof. exact (TRANS (@lem4108170 A n f h1) (@lem4108173)). Qed.
Lemma lem4108175 {A : Type'} (n : nat) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term397 A f n) = (term398 A n).
Proof. exact (MK_COMB (@lem4108131 A n f h1) (@lem4108174 A n f h1)). Qed.
Lemma lem4108177 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4108178 {A : Type'} (n : nat) : (term398 A n) = True.
Proof. exact (@lem4108177 (term387 A n)). Qed.
Lemma lem4108179 {A : Type'} (n : nat) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term397 A f n) = True.
Proof. exact (TRANS (@lem4108175 A n f h1) (@lem4108178 A n)). Qed.
Lemma lem4108180 {A : Type'} (n : nat) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : True = (term397 A f n).
Proof. exact (SYM (@lem4108179 A n f h1)). Qed.
Lemma lem4108181 {A : Type'} (n : nat) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : term397 A f n.
Proof. exact (EQ_MP (@lem4108180 A n f h1) (@lem0)). Qed.
Lemma lem4108242 {A : Type'} (f : type686 A) (n : nat) (h1 : term386 A f n) : term386 A f n.
Proof. exact (h1). Qed.
Lemma lem4108243 {A : Type'} (f : type686 A) (n : nat) (h1 : term384 A f n) : term384 A f n.
Proof. exact (h1). Qed.
Lemma lem4108244 {A : Type'} (f : type686 A) (h1 : term373 A f) : term373 A f.
Proof. exact (h1). Qed.
Lemma lem4108246 (t1 : Prop) (t2 : Prop) : (t2 -> t1) = (term342 t1 t2).
Proof. exact (EQ_MP (@lem4108025 t1 t2) (@lem4108024 t1 t2)). Qed.
Lemma lem4108247 {A : Type'} (f : type686 A) (n : nat) : (term399 A f n) = (term400 A f n).
Proof. exact (@lem4108246 (term396 A f n) (term384 A f n)). Qed.
Lemma lem4108248 {A : Type'} (f : type686 A) (n : nat) : (term400 A f n) = (term399 A f n).
Proof. exact (SYM (@lem4108247 A f n)). Qed.
Lemma lem4108252 (p : Prop) (q : Prop) : (term325 p q) = (term326 p q).
Proof. exact (or_elim (@lem4107914 p) (fun h0 : p = True => @lem4107994 q p h0) (fun h0 : p = False => @lem4107993 q p h0)). Qed.
Lemma lem4108253 {A : Type'} (f : type686 A) (n : nat) : (term401 A f n) = (term402 A f n).
Proof. exact (@lem4108252 (term390 A f) (term395 A f n)). Qed.
Lemma lem4108256 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4108257 {A : Type'} (f : type686 A) (n : nat) : (term403 A f n) = (term404 A f n).
Proof. exact (MK_COMB (@lem4108256) (@lem4108253 A f n)). Qed.
Lemma lem4108259 {A : Type'} (P : A -> Prop) : (term340 A P) = (term341 A P).
Proof. exact (EQ_MP (@lem4108005 A P) (@lem4108004 A P)). Qed.
Lemma lem4108260 {A : Type'} (P : type686 A) : (term405 A P) = (term406 A P).
Proof. exact (@lem4108259 (A -> Prop) P). Qed.
Lemma lem4108261 {A : Type'} (f : type686 A) (n : nat) : (term407 A f n) = (term408 A f n).
Proof. exact (@lem4108260 A (term382 A f n)). Qed.
Lemma lem4108262 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term409 A f n t) = (term380 A f t n).
Proof. exact (eq_refl (term409 A f n t)). Qed.
Lemma lem4108263 {A : Type'} (f : type686 A) (n : nat) : (term410 A f n) = (term382 A f n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4108262 A f t n)). Qed.
Lemma lem4108264 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4108265 {A : Type'} (f : type686 A) (n : nat) : (term411 A f n) = (term384 A f n).
Proof. exact (MK_COMB (@lem4108264 A) (@lem4108263 A f n)). Qed.
Lemma lem4108266 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4108267 {A : Type'} (f : type686 A) (n : nat) : (term407 A f n) = (term412 A f n).
Proof. exact (MK_COMB (@lem4108266) (@lem4108265 A f n)). Qed.
Lemma lem4108268 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4108269 {A : Type'} (f : type686 A) (n : nat) : (term413 A f n) = (term414 A f n).
Proof. exact (MK_COMB (@lem4108268) (@lem4108267 A f n)). Qed.
Lemma lem4108270 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term409 A f n t) = (term380 A f t n).
Proof. exact (eq_refl (term409 A f n t)). Qed.
Lemma lem4108271 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4108272 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term415 A f n t) = (term416 A f t n).
Proof. exact (MK_COMB (@lem4108271) (@lem4108270 A f t n)). Qed.
Lemma lem4108273 {A : Type'} (f : type686 A) (n : nat) : (term417 A f n) = (term418 A f n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4108272 A f t n)). Qed.
Lemma lem4108274 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4108275 {A : Type'} (f : type686 A) (n : nat) : (term408 A f n) = (term419 A f n).
Proof. exact (MK_COMB (@lem4108274 A) (@lem4108273 A f n)). Qed.
Lemma lem4108276 {A : Type'} (f : type686 A) (n : nat) : ((term407 A f n) = (term408 A f n)) = ((term412 A f n) = (term419 A f n)).
Proof. exact (MK_COMB (@lem4108269 A f n) (@lem4108275 A f n)). Qed.
Lemma lem4108277 {A : Type'} (f : type686 A) (n : nat) : (term412 A f n) = (term419 A f n).
Proof. exact (EQ_MP (@lem4108276 A f n) (@lem4108261 A f n)). Qed.
Lemma lem4108283 (t1 : Prop) (t2 : Prop) : (term337 t1 t2) = (term338 t1 t2).
Proof. exact (EQ_MP (@lem4108002 t1 t2) (@lem4108001 t1 t2)). Qed.
Lemma lem4108284 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term416 A f t n) = (term420 A f t n).
Proof. exact (@lem4108283 (@IN (A -> Prop) t f) (term379 A t n)). Qed.
Lemma lem4108288 (p : Prop) (q : Prop) : (term325 p q) = (term326 p q).
Proof. exact (or_elim (@lem4107914 p) (fun h0 : p = True => @lem4107994 q p h0) (fun h0 : p = False => @lem4107993 q p h0)). Qed.
Lemma lem4108289 {A : Type'} (t : A -> Prop) (n : nat) : (term421 A t n) = (term422 A t n).
Proof. exact (@lem4108288 (@FINITE A t) (term423 A t n)). Qed.
Lemma lem4108292 {A : Type'} (t : A -> Prop) (f : type686 A) : (term358 A t f) = (term358 A t f).
Proof. exact (eq_refl (term358 A t f)). Qed.
Lemma lem4108293 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term420 A f t n) = (term424 A f t n).
Proof. exact (MK_COMB (@lem4108292 A t f) (@lem4108289 A t n)). Qed.
Lemma lem4108296 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term416 A f t n) = (term424 A f t n).
Proof. exact (TRANS (@lem4108284 A f t n) (@lem4108293 A f t n)). Qed.
Lemma lem4108297 {A : Type'} (f : type686 A) (n : nat) : (term418 A f n) = (term425 A f n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4108296 A f t n)). Qed.
Lemma lem4108298 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4108299 {A : Type'} (f : type686 A) (n : nat) : (term419 A f n) = (term426 A f n).
Proof. exact (MK_COMB (@lem4108298 A) (@lem4108297 A f n)). Qed.
Lemma lem4108304 {A : Type'} (f : type686 A) (n : nat) : (term412 A f n) = (term426 A f n).
Proof. exact (TRANS (@lem4108277 A f n) (@lem4108299 A f n)). Qed.
Lemma lem4108305 {A : Type'} (f : type686 A) (n : nat) : (term400 A f n) = (term427 A f n).
Proof. exact (MK_COMB (@lem4108257 A f n) (@lem4108304 A f n)). Qed.
Lemma lem4108308 {A : Type'} (f : type686 A) (n : nat) : (term427 A f n) = (term400 A f n).
Proof. exact (SYM (@lem4108305 A f n)). Qed.
Lemma lem4108314 (n : nat) (x : nat) : (term40 x n) = (term41 n x).
Proof. exact (EQ_MP (@lem4107902 n x) (@lem4107901 n x)). Qed.
Lemma lem4108315 {A : Type'} (n : nat) (f : type686 A) : (term428 A f n) = (term429 A n f).
Proof. exact (@lem4108314 n (term392 A f)). Qed.
Lemma lem4108316 {A : Type'} (f : type686 A) : (term430 A f) = (term430 A f).
Proof. exact (eq_refl (term430 A f)). Qed.
Lemma lem4108317 {A : Type'} (n : nat) (f : type686 A) : (term402 A f n) = (term431 A n f).
Proof. exact (MK_COMB (@lem4108316 A f) (@lem4108315 A n f)). Qed.
Lemma lem4108320 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4108321 {A : Type'} (n : nat) (f : type686 A) : (term404 A f n) = (term432 A n f).
Proof. exact (MK_COMB (@lem4108320) (@lem4108317 A n f)). Qed.
Lemma lem4108331 (n : nat) (x : nat) : (term40 x n) = (term41 n x).
Proof. exact (EQ_MP (@lem4107902 n x) (@lem4107901 n x)). Qed.
Lemma lem4108332 {A : Type'} (n : nat) (t : A -> Prop) : (term433 A t n) = (term434 A n t).
Proof. exact (@lem4108331 n (@CARD A t)). Qed.
Lemma lem4108333 {A : Type'} (t : A -> Prop) : (term435 A t) = (term435 A t).
Proof. exact (eq_refl (term435 A t)). Qed.
Lemma lem4108334 {A : Type'} (n : nat) (t : A -> Prop) : (term422 A t n) = (term436 A n t).
Proof. exact (MK_COMB (@lem4108333 A t) (@lem4108332 A n t)). Qed.
Lemma lem4108337 {A : Type'} (t : A -> Prop) (f : type686 A) : (term358 A t f) = (term358 A t f).
Proof. exact (eq_refl (term358 A t f)). Qed.
Lemma lem4108338 {A : Type'} (f : type686 A) (n : nat) (t : A -> Prop) : (term424 A f t n) = (term437 A f n t).
Proof. exact (MK_COMB (@lem4108337 A t f) (@lem4108334 A n t)). Qed.
Lemma lem4108341 {A : Type'} (f : type686 A) (n : nat) : (term425 A f n) = (term438 A f n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4108338 A f n t)). Qed.
Lemma lem4108342 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4108343 {A : Type'} (f : type686 A) (n : nat) : (term426 A f n) = (term439 A f n).
Proof. exact (MK_COMB (@lem4108342 A) (@lem4108341 A f n)). Qed.
Lemma lem4108348 {A : Type'} (f : type686 A) (n : nat) : (term427 A f n) = (term440 A f n).
Proof. exact (MK_COMB (@lem4108321 A n f) (@lem4108343 A f n)). Qed.
Lemma lem4108351 {A : Type'} (f : type686 A) (n : nat) : (term440 A f n) = (term427 A f n).
Proof. exact (SYM (@lem4108348 A f n)). Qed.
Lemma lem4108355 {A : Type'} (s : A -> Prop) (n : nat) : (term29 A n s) = (term30 A s n).
Proof. exact (EQ_MP (@lem4106094 A s n) (@lem4106093 A n s)). Qed.
Lemma lem4108356 {A : Type'} (s : A -> Prop) (n : nat) : (term29 A n s) = (term30 A s n).
Proof. exact (@lem4108355 A s n). Qed.
Lemma lem4108357 {A : Type'} (f : type686 A) (n : nat) : (term431 A n f) = (term441 A f n).
Proof. exact (@lem4108356 A (@UNIONS A f) (S n)). Qed.
Lemma lem4108364 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4108365 {A : Type'} (f : type686 A) (n : nat) : (term432 A n f) = (term442 A f n).
Proof. exact (MK_COMB (@lem4108364) (@lem4108357 A f n)). Qed.
Lemma lem4108373 {A : Type'} (s : A -> Prop) (n : nat) : (term29 A n s) = (term30 A s n).
Proof. exact (EQ_MP (@lem4106094 A s n) (@lem4106093 A n s)). Qed.
Lemma lem4108374 {A : Type'} (s : A -> Prop) (n : nat) : (term29 A n s) = (term30 A s n).
Proof. exact (@lem4108373 A s n). Qed.
Lemma lem4108375 {A : Type'} (t : A -> Prop) (n : nat) : (term436 A n t) = (term443 A t n).
Proof. exact (@lem4108374 A t (S n)). Qed.
Lemma lem4108382 {A : Type'} (t : A -> Prop) (f : type686 A) : (term358 A t f) = (term358 A t f).
Proof. exact (eq_refl (term358 A t f)). Qed.
Lemma lem4108383 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term437 A f n t) = (term444 A f t n).
Proof. exact (MK_COMB (@lem4108382 A t f) (@lem4108375 A t n)). Qed.
Lemma lem4108386 {A : Type'} (f : type686 A) (n : nat) : (term438 A f n) = (term445 A f n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4108383 A f t n)). Qed.
Lemma lem4108387 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4108388 {A : Type'} (f : type686 A) (n : nat) : (term439 A f n) = (term446 A f n).
Proof. exact (MK_COMB (@lem4108387 A) (@lem4108386 A f n)). Qed.
Lemma lem4108393 {A : Type'} (f : type686 A) (n : nat) : (term440 A f n) = (term447 A f n).
Proof. exact (MK_COMB (@lem4108365 A f n) (@lem4108388 A f n)). Qed.
Lemma lem4108396 {A : Type'} (f : type686 A) (n : nat) : (term447 A f n) = (term440 A f n).
Proof. exact (SYM (@lem4108393 A f n)). Qed.
Lemma lem4108410 {A : Type'} (P : Prop) (Q : A -> Prop) : (term24 A P Q) = (term25 A P Q).
Proof. exact (EQ_MP (@lem4106088 A P Q) (@lem4106087 A P Q)). Qed.
Lemma lem4108411 {A : Type'} (P : Prop) (Q : type686 A) : (term448 A P Q) = (term449 A P Q).
Proof. exact (@lem4108410 (A -> Prop) P Q). Qed.
Lemma lem4108412 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term450 A f t n) = (term451 A f t n).
Proof. exact (@lem4108411 A (@IN (A -> Prop) t f) (term452 A t n)). Qed.
Lemma lem4108413 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (n : nat) : (term453 A t n t') = (term454 A t t' n).
Proof. exact (eq_refl (term453 A t n t')). Qed.
Lemma lem4108414 {A : Type'} (t : A -> Prop) (n : nat) : (term455 A t n) = (term452 A t n).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4108413 A t t' n)). Qed.
Lemma lem4108415 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4108416 {A : Type'} (t : A -> Prop) (n : nat) : (term456 A t n) = (term443 A t n).
Proof. exact (MK_COMB (@lem4108415 A) (@lem4108414 A t n)). Qed.
Lemma lem4108417 {A : Type'} (t : A -> Prop) (f : type686 A) : (term358 A t f) = (term358 A t f).
Proof. exact (eq_refl (term358 A t f)). Qed.
Lemma lem4108418 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term450 A f t n) = (term444 A f t n).
Proof. exact (MK_COMB (@lem4108417 A t f) (@lem4108416 A t n)). Qed.
Lemma lem4108419 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4108420 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term457 A f t n) = (term458 A f t n).
Proof. exact (MK_COMB (@lem4108419) (@lem4108418 A f t n)). Qed.
Lemma lem4108421 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (n : nat) : (term453 A t n t') = (term454 A t t' n).
Proof. exact (eq_refl (term453 A t n t')). Qed.
Lemma lem4108422 {A : Type'} (t : A -> Prop) (f : type686 A) : (term358 A t f) = (term358 A t f).
Proof. exact (eq_refl (term358 A t f)). Qed.
Lemma lem4108423 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) (n : nat) : (term459 A f t n t') = (term460 A f t t' n).
Proof. exact (MK_COMB (@lem4108422 A t f) (@lem4108421 A t t' n)). Qed.
Lemma lem4108424 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term461 A f t n) = (term462 A f t n).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4108423 A f t t' n)). Qed.
Lemma lem4108425 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4108426 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term451 A f t n) = (term463 A f t n).
Proof. exact (MK_COMB (@lem4108425 A) (@lem4108424 A f t n)). Qed.
Lemma lem4108427 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : ((term450 A f t n) = (term451 A f t n)) = ((term444 A f t n) = (term463 A f t n)).
Proof. exact (MK_COMB (@lem4108420 A f t n) (@lem4108426 A f t n)). Qed.
Lemma lem4108428 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term444 A f t n) = (term463 A f t n).
Proof. exact (EQ_MP (@lem4108427 A f t n) (@lem4108412 A f t n)). Qed.
Lemma lem4108437 {A : Type'} (f : type686 A) (n : nat) : (term445 A f n) = (term464 A f n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4108428 A f t n)). Qed.
Lemma lem4108438 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4108439 {A : Type'} (f : type686 A) (n : nat) : (term446 A f n) = (term465 A f n).
Proof. exact (MK_COMB (@lem4108438 A) (@lem4108437 A f n)). Qed.
Lemma lem4108444 {A : Type'} (f : type686 A) (n : nat) : (term442 A f n) = (term442 A f n).
Proof. exact (eq_refl (term442 A f n)). Qed.
Lemma lem4108445 {A : Type'} (f : type686 A) (n : nat) : (term447 A f n) = (term466 A f n).
Proof. exact (MK_COMB (@lem4108444 A f n) (@lem4108439 A f n)). Qed.
Lemma lem4108448 {A : Type'} (f : type686 A) (n : nat) : (term466 A f n) = (term447 A f n).
Proof. exact (SYM (@lem4108445 A f n)). Qed.
Lemma lem4108458 {A B : Type'} (P : type1413 A B) : (term19 A B P) = (term20 A B P).
Proof. exact (EQ_MP (@lem4106082 A B P) (@lem4106081 A B P)). Qed.
Lemma lem4108459 {A : Type'} (P : type639 A) : (term467 A P) = (term468 A P).
Proof. exact (@lem4108458 (A -> Prop) (A -> Prop) P). Qed.
Lemma lem4108460 {A : Type'} (f : type686 A) (n : nat) : (term469 A f n) = (term470 A f n).
Proof. exact (@lem4108459 A (term471 A f n)). Qed.
Lemma lem4108461 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term472 A f n t) = (term462 A f t n).
Proof. exact (eq_refl (term472 A f n t)). Qed.
Lemma lem4108462 {A : Type'} (t' : A -> Prop) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem4108463 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) (t' : A -> Prop) : (term473 A f n t t') = (term474 A f t n t').
Proof. exact (MK_COMB (@lem4108461 A f t n) (@lem4108462 A t')). Qed.
Lemma lem4108464 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) (n : nat) : (term474 A f t n t') = (term460 A f t t' n).
Proof. exact (eq_refl (term474 A f t n t')). Qed.
Lemma lem4108465 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) (n : nat) : (term473 A f n t t') = (term460 A f t t' n).
Proof. exact (TRANS (@lem4108463 A f t n t') (@lem4108464 A f t t' n)). Qed.
Lemma lem4108466 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term475 A f n t) = (term462 A f t n).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4108465 A f t t' n)). Qed.
Lemma lem4108467 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4108468 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term476 A f n t) = (term463 A f t n).
Proof. exact (MK_COMB (@lem4108467 A) (@lem4108466 A f t n)). Qed.
Lemma lem4108469 {A : Type'} (f : type686 A) (n : nat) : (term477 A f n) = (term464 A f n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4108468 A f t n)). Qed.
Lemma lem4108470 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4108471 {A : Type'} (f : type686 A) (n : nat) : (term469 A f n) = (term465 A f n).
Proof. exact (MK_COMB (@lem4108470 A) (@lem4108469 A f n)). Qed.
Lemma lem4108472 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4108473 {A : Type'} (f : type686 A) (n : nat) : (term478 A f n) = (term479 A f n).
Proof. exact (MK_COMB (@lem4108472) (@lem4108471 A f n)). Qed.
Lemma lem4108474 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term472 A f n t) = (term462 A f t n).
Proof. exact (eq_refl (term472 A f n t)). Qed.
Lemma lem4108475 {A : Type'} (t' : A -> Prop) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem4108476 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) (t' : A -> Prop) : (term473 A f n t t') = (term474 A f t n t').
Proof. exact (MK_COMB (@lem4108474 A f t n) (@lem4108475 A t')). Qed.
Lemma lem4108477 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) (n : nat) : (term474 A f t n t') = (term460 A f t t' n).
Proof. exact (eq_refl (term474 A f t n t')). Qed.
Lemma lem4108478 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) (n : nat) : (term473 A f n t t') = (term460 A f t t' n).
Proof. exact (TRANS (@lem4108476 A f t n t') (@lem4108477 A f t t' n)). Qed.
Lemma lem4108479 {A : Type'} (f : type686 A) (t' : A -> Prop) (n : nat) : (term480 A f n t') = (term481 A f t' n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4108478 A f t t' n)). Qed.
Lemma lem4108480 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4108481 {A : Type'} (f : type686 A) (t' : A -> Prop) (n : nat) : (term482 A f n t') = (term483 A f t' n).
Proof. exact (MK_COMB (@lem4108480 A) (@lem4108479 A f t' n)). Qed.
Lemma lem4108482 {A : Type'} (f : type686 A) (n : nat) : (term484 A f n) = (term485 A f n).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4108481 A f t' n)). Qed.
Lemma lem4108483 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4108484 {A : Type'} (f : type686 A) (n : nat) : (term470 A f n) = (term486 A f n).
Proof. exact (MK_COMB (@lem4108483 A) (@lem4108482 A f n)). Qed.
Lemma lem4108485 {A : Type'} (f : type686 A) (n : nat) : ((term469 A f n) = (term470 A f n)) = ((term465 A f n) = (term486 A f n)).
Proof. exact (MK_COMB (@lem4108473 A f n) (@lem4108484 A f n)). Qed.
Lemma lem4108486 {A : Type'} (f : type686 A) (n : nat) : (term465 A f n) = (term486 A f n).
Proof. exact (EQ_MP (@lem4108485 A f n) (@lem4108460 A f n)). Qed.
Lemma lem4108487 {A : Type'} (f : type686 A) (n : nat) : (term442 A f n) = (term442 A f n).
Proof. exact (eq_refl (term442 A f n)). Qed.
Lemma lem4108488 {A : Type'} (f : type686 A) (n : nat) : (term466 A f n) = (term487 A f n).
Proof. exact (MK_COMB (@lem4108487 A f n) (@lem4108486 A f n)). Qed.
Lemma lem4108489 {A : Type'} (f : type686 A) (n : nat) : (term487 A f n) = (term466 A f n).
Proof. exact (SYM (@lem4108488 A f n)). Qed.
Lemma lem4108491 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term13 A P Q.
Proof. exact (@lem4106079 A P Q (@lem7401 A P Q)). Qed.
Lemma lem4108492 {A : Type'} (P : type686 A) (Q : type686 A) : term488 A P Q.
Proof. exact (@lem4108491 (A -> Prop) P Q). Qed.
Lemma lem4108493 {A : Type'} (f : type686 A) (n : nat) : term489 A f n.
Proof. exact (@lem4108492 A (term490 A f n) (term485 A f n)). Qed.
Lemma lem4108494 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term491 A f n t) = (term492 A f t n).
Proof. exact (eq_refl (term491 A f n t)). Qed.
Lemma lem4108495 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4108496 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term493 A f n t) = (term494 A f t n).
Proof. exact (MK_COMB (@lem4108495) (@lem4108494 A f t n)). Qed.
Lemma lem4108497 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term495 A f n t) = (term483 A f t n).
Proof. exact (eq_refl (term495 A f n t)). Qed.
Lemma lem4108498 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term496 A f n t) = (term497 A f t n).
Proof. exact (MK_COMB (@lem4108496 A f t n) (@lem4108497 A f t n)). Qed.
Lemma lem4108499 {A : Type'} (f : type686 A) (n : nat) : (term498 A f n) = (term499 A f n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4108498 A f t n)). Qed.
Lemma lem4108500 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4108501 {A : Type'} (f : type686 A) (n : nat) : (term500 A f n) = (term501 A f n).
Proof. exact (MK_COMB (@lem4108500 A) (@lem4108499 A f n)). Qed.
Lemma lem4108502 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4108503 {A : Type'} (f : type686 A) (n : nat) : (term502 A f n) = (term503 A f n).
Proof. exact (MK_COMB (@lem4108502) (@lem4108501 A f n)). Qed.
Lemma lem4108504 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term491 A f n t) = (term492 A f t n).
Proof. exact (eq_refl (term491 A f n t)). Qed.
Lemma lem4108505 {A : Type'} (f : type686 A) (n : nat) : (term504 A f n) = (term490 A f n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4108504 A f t n)). Qed.
Lemma lem4108506 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4108507 {A : Type'} (f : type686 A) (n : nat) : (term505 A f n) = (term441 A f n).
Proof. exact (MK_COMB (@lem4108506 A) (@lem4108505 A f n)). Qed.
Lemma lem4108508 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4108509 {A : Type'} (f : type686 A) (n : nat) : (term506 A f n) = (term442 A f n).
Proof. exact (MK_COMB (@lem4108508) (@lem4108507 A f n)). Qed.
Lemma lem4108510 {A : Type'} (f : type686 A) (t : A -> Prop) (n : nat) : (term495 A f n t) = (term483 A f t n).
Proof. exact (eq_refl (term495 A f n t)). Qed.
Lemma lem4108511 {A : Type'} (f : type686 A) (n : nat) : (term507 A f n) = (term485 A f n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4108510 A f t n)). Qed.
Lemma lem4108512 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4108513 {A : Type'} (f : type686 A) (n : nat) : (term508 A f n) = (term486 A f n).
Proof. exact (MK_COMB (@lem4108512 A) (@lem4108511 A f n)). Qed.
Lemma lem4108514 {A : Type'} (f : type686 A) (n : nat) : (term509 A f n) = (term487 A f n).
Proof. exact (MK_COMB (@lem4108509 A f n) (@lem4108513 A f n)). Qed.
Lemma lem4108515 {A : Type'} (f : type686 A) (n : nat) : (term489 A f n) = (term510 A f n).
Proof. exact (MK_COMB (@lem4108503 A f n) (@lem4108514 A f n)). Qed.
Lemma lem4108516 {A : Type'} (f : type686 A) (n : nat) : term510 A f n.
Proof. exact (EQ_MP (@lem4108515 A f n) (@lem4108493 A f n)). Qed.
Lemma lem4108519 {A : Type'} (f : type686 A) (n : nat) : (term511 A f n) = (term511 A f n).
Proof. exact (eq_refl (term511 A f n)). Qed.
Lemma lem4108520 {A : Type'} (f : type686 A) (n : nat) : (term511 A f n) = (term510 A f n).
Proof. exact (eq_refl (term511 A f n)). Qed.
Lemma lem4108521 {A : Type'} (f : type686 A) (n : nat) : (term512 A f n) = (term512 A f n).
Proof. exact (eq_refl (term512 A f n)). Qed.
Lemma lem4108522 {A : Type'} (f : type686 A) (n : nat) : ((term511 A f n) = (term511 A f n)) = ((term511 A f n) = (term510 A f n)).
Proof. exact (MK_COMB (@lem4108521 A f n) (@lem4108520 A f n)). Qed.
Lemma lem4108523 {A : Type'} (f : type686 A) (n : nat) : (term511 A f n) = (term510 A f n).
Proof. exact (eq_refl (term511 A f n)). Qed.
Lemma lem4108524 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4108525 {A : Type'} (f : type686 A) (n : nat) : (term512 A f n) = (term513 A f n).
Proof. exact (MK_COMB (@lem4108524) (@lem4108523 A f n)). Qed.
Lemma lem4108526 {A : Type'} (f : type686 A) (n : nat) : (term510 A f n) = (term510 A f n).
Proof. exact (eq_refl (term510 A f n)). Qed.
Lemma lem4108527 {A : Type'} (f : type686 A) (n : nat) : ((term511 A f n) = (term510 A f n)) = ((term510 A f n) = (term510 A f n)).
Proof. exact (MK_COMB (@lem4108525 A f n) (@lem4108526 A f n)). Qed.
Lemma lem4108528 {A : Type'} (f : type686 A) (n : nat) : ((term511 A f n) = (term511 A f n)) = ((term510 A f n) = (term510 A f n)).
Proof. exact (TRANS (@lem4108522 A f n) (@lem4108527 A f n)). Qed.
Lemma lem4108529 {A : Type'} (f : type686 A) (n : nat) : (term510 A f n) = (term510 A f n).
Proof. exact (EQ_MP (@lem4108528 A f n) (@lem4108519 A f n)). Qed.
Lemma lem4108530 {A : Type'} (f : type686 A) (n : nat) : term510 A f n.
Proof. exact (EQ_MP (@lem4108529 A f n) (@lem4108516 A f n)). Qed.
Lemma lem4108536 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term12 _100044 s n).
Proof. exact (EQ_MP (@lem4106070 _100044 s n) (@lem4106069 _100044 s n)). Qed.
Lemma lem4108537 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (term12 A s n).
Proof. exact (@lem4108536 A s n). Qed.
Lemma lem4108538 {A : Type'} (s : A -> Prop) (n : nat) : (term514 A s n) = (term515 A s n).
Proof. exact (@lem4108537 A s (S n)). Qed.
Lemma lem4108543 {A : Type'} (s : A -> Prop) (f : type686 A) : (term516 A s f) = (term516 A s f).
Proof. exact (eq_refl (term516 A s f)). Qed.
Lemma lem4108544 {A : Type'} (f : type686 A) (s : A -> Prop) (n : nat) : (term492 A f s n) = (term517 A f s n).
Proof. exact (MK_COMB (@lem4108543 A s f) (@lem4108538 A s n)). Qed.
Lemma lem4108547 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4108548 {A : Type'} (f : type686 A) (s : A -> Prop) (n : nat) : (term494 A f s n) = (term518 A f s n).
Proof. exact (MK_COMB (@lem4108547) (@lem4108544 A f s n)). Qed.
Lemma lem4108558 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term12 _100044 s n).
Proof. exact (EQ_MP (@lem4106070 _100044 s n) (@lem4106069 _100044 s n)). Qed.
Lemma lem4108559 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (term12 A s n).
Proof. exact (@lem4108558 A s n). Qed.
Lemma lem4108560 {A : Type'} (s : A -> Prop) (n : nat) : (term514 A s n) = (term515 A s n).
Proof. exact (@lem4108559 A s (S n)). Qed.
Lemma lem4108565 {A : Type'} (s : A -> Prop) (t' : A -> Prop) : (term519 A s t') = (term519 A s t').
Proof. exact (eq_refl (term519 A s t')). Qed.
Lemma lem4108566 {A : Type'} (t' : A -> Prop) (s : A -> Prop) (n : nat) : (term454 A t' s n) = (term520 A t' s n).
Proof. exact (MK_COMB (@lem4108565 A s t') (@lem4108560 A s n)). Qed.
Lemma lem4108569 {A : Type'} (t' : A -> Prop) (f : type686 A) : (term358 A t' f) = (term358 A t' f).
Proof. exact (eq_refl (term358 A t' f)). Qed.
Lemma lem4108570 {A : Type'} (f : type686 A) (t' : A -> Prop) (s : A -> Prop) (n : nat) : (term460 A f t' s n) = (term521 A f t' s n).
Proof. exact (MK_COMB (@lem4108569 A t' f) (@lem4108566 A t' s n)). Qed.
Lemma lem4108573 {A : Type'} (f : type686 A) (s : A -> Prop) (n : nat) : (term481 A f s n) = (term522 A f s n).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4108570 A f t' s n)). Qed.
Lemma lem4108574 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4108575 {A : Type'} (f : type686 A) (s : A -> Prop) (n : nat) : (term483 A f s n) = (term523 A f s n).
Proof. exact (MK_COMB (@lem4108574 A) (@lem4108573 A f s n)). Qed.
Lemma lem4108580 {A : Type'} (f : type686 A) (s : A -> Prop) (n : nat) : (term497 A f s n) = (term524 A f s n).
Proof. exact (MK_COMB (@lem4108548 A f s n) (@lem4108575 A f s n)). Qed.
Lemma lem4108583 {A : Type'} (f : type686 A) (s : A -> Prop) (n : nat) : (term524 A f s n) = (term497 A f s n).
Proof. exact (SYM (@lem4108580 A f s n)). Qed.
Lemma lem4108584 {A : Type'} (f : type686 A) (s : A -> Prop) (n : nat) (h1 : term517 A f s n) : term517 A f s n.
Proof. exact (h1). Qed.
Lemma lem4108585 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term515 A s n) : term515 A s n.
Proof. exact (h1). Qed.
Lemma lem4108586 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term525 A s f) : term525 A s f.
Proof. exact (h1). Qed.
Lemma lem4108587 {A : Type'} (s : A -> Prop) (n : nat) (h1 : (@CARD A s) = (S n)) : (@CARD A s) = (S n).
Proof. exact (h1). Qed.
Lemma lem4108588 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4108612 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem4108625 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4108612 A s) (@lem4108588 A s h1)). Qed.
Lemma lem4108626 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4108627 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term526 A s) = (and True).
Proof. exact (MK_COMB (@lem4108626) (@lem4108625 A s h1)). Qed.
Lemma lem4108631 {A : Type'} (s : A -> Prop) (n : nat) (h1 : (@CARD A s) = (S n)) : (@CARD A s) = (S n).
Proof. exact (h1). Qed.
Lemma lem4108632 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4108633 {A : Type'} (s : A -> Prop) (n : nat) (h1 : (@CARD A s) = (S n)) : (term527 A s) = (term528 n).
Proof. exact (MK_COMB (@lem4108632) (@lem4108631 A s n h1)). Qed.
Lemma lem4108634 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem4108635 {A : Type'} (s : A -> Prop) (n : nat) (h1 : (@CARD A s) = (S n)) : ((@CARD A s) = (S n)) = ((S n) = (S n)).
Proof. exact (MK_COMB (@lem4108633 A s n h1) (@lem4108634 n)). Qed.
Lemma lem4108637 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4108638 (x : nat) : (x = x) = True.
Proof. exact (@lem4108637 nat x). Qed.
Lemma lem4108639 (n : nat) : ((S n) = (S n)) = True.
Proof. exact (@lem4108638 (S n)). Qed.
Lemma lem4108640 {A : Type'} (s : A -> Prop) (n : nat) (h1 : (@CARD A s) = (S n)) : ((@CARD A s) = (S n)) = True.
Proof. exact (TRANS (@lem4108635 A s n h1) (@lem4108639 n)). Qed.
Lemma lem4108641 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @FINITE A s) (h2 : (@CARD A s) = (S n)) : (term515 A s n) = (True /\ True).
Proof. exact (MK_COMB (@lem4108627 A s h1) (@lem4108640 A s n h2)). Qed.
Lemma lem4108643 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4108644 : (True /\ True) = True.
Proof. exact (@lem4108643 True). Qed.
Lemma lem4108645 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @FINITE A s) (h2 : (@CARD A s) = (S n)) : (term515 A s n) = True.
Proof. exact (TRANS (@lem4108641 A s n h1 h2) (@lem4108644)). Qed.
Lemma lem4108646 {A : Type'} (s : A -> Prop) (t' : A -> Prop) : (term519 A s t') = (term519 A s t').
Proof. exact (eq_refl (term519 A s t')). Qed.
Lemma lem4108647 {A : Type'} (t' : A -> Prop) (s : A -> Prop) (n : nat) (h1 : @FINITE A s) (h2 : (@CARD A s) = (S n)) : (term520 A t' s n) = (term529 A s t').
Proof. exact (MK_COMB (@lem4108646 A s t') (@lem4108645 A s n h1 h2)). Qed.
Lemma lem4108649 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4108650 {A : Type'} (s : A -> Prop) (t' : A -> Prop) : (term529 A s t') = (@SUBSET A s t').
Proof. exact (@lem4108649 (@SUBSET A s t')). Qed.
Lemma lem4108651 {A : Type'} (t' : A -> Prop) (s : A -> Prop) (n : nat) (h1 : @FINITE A s) (h2 : (@CARD A s) = (S n)) : (term520 A t' s n) = (@SUBSET A s t').
Proof. exact (TRANS (@lem4108647 A t' s n h1 h2) (@lem4108650 A s t')). Qed.
Lemma lem4108652 {A : Type'} (t' : A -> Prop) (f : type686 A) : (term358 A t' f) = (term358 A t' f).
Proof. exact (eq_refl (term358 A t' f)). Qed.
Lemma lem4108653 {A : Type'} (f : type686 A) (t' : A -> Prop) (s : A -> Prop) (n : nat) (h1 : @FINITE A s) (h2 : (@CARD A s) = (S n)) : (term521 A f t' s n) = (term530 A f s t').
Proof. exact (MK_COMB (@lem4108652 A t' f) (@lem4108651 A t' s n h1 h2)). Qed.
Lemma lem4108656 {A : Type'} (f : type686 A) (s : A -> Prop) (n : nat) (h1 : @FINITE A s) (h2 : (@CARD A s) = (S n)) : (term522 A f s n) = (term531 A f s).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4108653 A f t' s n h1 h2)). Qed.
Lemma lem4108657 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4108658 {A : Type'} (f : type686 A) (s : A -> Prop) (n : nat) (h1 : @FINITE A s) (h2 : (@CARD A s) = (S n)) : (term523 A f s n) = (term6 A f s).
Proof. exact (MK_COMB (@lem4108657 A) (@lem4108656 A f s n h1 h2)). Qed.
Lemma lem4108663 {A : Type'} (f : type686 A) (s : A -> Prop) (n : nat) (h1 : @FINITE A s) (h2 : (@CARD A s) = (S n)) : (term6 A f s) = (term523 A f s n).
Proof. exact (SYM (@lem4108658 A f s n h1 h2)). Qed.
Lemma lem4108665 {A : Type'} (f : type686 A) (s : A -> Prop) : term4 A f s.
Proof. exact (EQ_MP (@lem4106064 A f s) (@lem4106063 A f s)). Qed.
Lemma lem4108666 {A : Type'} (f : type686 A) (s : A -> Prop) : term4 A f s.
Proof. exact (@lem4108665 A f s). Qed.
Lemma lem4108667 {A : Type'} (f : type686 A) : term532 A f.
Proof. exact (@lem82 (f = (@EMPTY (A -> Prop)))). Qed.
Lemma lem4108680 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term373 A f) : term533 A f t.
Proof. exact (@lem4108244 A f h1 t). Qed.
Lemma lem4108681 {A : Type'} (f : type686 A) (t : A -> Prop) : (term533 A f t) = (term369 A f t).
Proof. exact (eq_refl (term533 A f t)). Qed.
Lemma lem4108682 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term373 A f) : term369 A f t.
Proof. exact (EQ_MP (@lem4108681 A f t) (@lem4108680 A t f h1)). Qed.
Lemma lem4108683 {A : Type'} (t : A -> Prop) (u : A -> Prop) (f : type686 A) (h1 : term373 A f) : term534 A f t u.
Proof. exact (@lem4108682 A t f h1 u). Qed.
Lemma lem4108684 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term534 A f t u) = (term365 A f u t).
Proof. exact (eq_refl (term534 A f t u)). Qed.
Lemma lem4108685 {A : Type'} (u : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term373 A f) : term365 A f u t.
Proof. exact (EQ_MP (@lem4108684 A f u t) (@lem4108683 A t u f h1)). Qed.
Lemma lem4108686 {A : Type'} (f : type686 A) (u : A -> Prop) (t : A -> Prop) : (term365 A f u t) = ((term365 A f u t) = True).
Proof. exact (@lem7 (term365 A f u t)). Qed.
Lemma lem4108688 {A : Type'} (s : A -> Prop) (f : type686 A) : (term525 A s f) = ((term525 A s f) = True).
Proof. exact (@lem7 (term525 A s f)). Qed.
Lemma lem4108690 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem4108695 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4108690 A s) (@lem4108588 A s h1)). Qed.
Lemma lem4108696 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4108697 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term526 A s) = (and True).
Proof. exact (MK_COMB (@lem4108696) (@lem4108695 A s h1)). Qed.
Lemma lem4108701 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term525 A s f) : (term525 A s f) = True.
Proof. exact (EQ_MP (@lem4108688 A s f) (@lem4108586 A s f h1)). Qed.
Lemma lem4108702 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4108703 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term525 A s f) : (term516 A s f) = (and True).
Proof. exact (MK_COMB (@lem4108702) (@lem4108701 A s f h1)). Qed.
Lemma lem4108707 {A : Type'} (f : type686 A) (h1 : term355 A f) : (f = (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem4108667 A f (@lem4108031 A f h1)). Qed.
Lemma lem4108708 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4108709 {A : Type'} (f : type686 A) (h1 : term355 A f) : (term355 A f) = (~ False).
Proof. exact (MK_COMB (@lem4108708) (@lem4108707 A f h1)). Qed.
Lemma lem4108711 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4108712 {A : Type'} (f : type686 A) (h1 : term355 A f) : (term355 A f) = True.
Proof. exact (TRANS (@lem4108709 A f h1) (@lem4108711)). Qed.
Lemma lem4108713 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4108714 {A : Type'} (f : type686 A) (h1 : term355 A f) : (term535 A f) = (and True).
Proof. exact (MK_COMB (@lem4108713) (@lem4108712 A f h1)). Qed.
Lemma lem4108724 {A : Type'} (u : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term373 A f) : (term365 A f u t) = True.
Proof. exact (EQ_MP (@lem4108686 A f u t) (@lem4108685 A u t f h1)). Qed.
Lemma lem4108725 {A : Type'} (u : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term373 A f) : (term365 A f u t) = True.
Proof. exact (@lem4108724 A u t f h1). Qed.
Lemma lem4108726 {A : Type'} (u : A -> Prop) (t' : A -> Prop) (f : type686 A) (h1 : term373 A f) : (term365 A f u t') = True.
Proof. exact (@lem4108725 A u t' f h1). Qed.
Lemma lem4108727 {A : Type'} (t' : A -> Prop) (f : type686 A) (h1 : term373 A f) : (term367 A f t') = (term536 A).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4108726 A u t' f h1)). Qed.
Lemma lem4108728 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4108729 {A : Type'} (t' : A -> Prop) (f : type686 A) (h1 : term373 A f) : (term369 A f t') = (term537 A).
Proof. exact (MK_COMB (@lem4108728 A) (@lem4108727 A t' f h1)). Qed.
Lemma lem4108731 {A : Type'} (t : Prop) : (term538 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4108732 {A : Type'} (t : Prop) : (term539 A t) = t.
Proof. exact (@lem4108731 (A -> Prop) t). Qed.
Lemma lem4108733 {A : Type'} : (term537 A) = True.
Proof. exact (@lem4108732 A True). Qed.
Lemma lem4108734 {A : Type'} (t' : A -> Prop) (f : type686 A) (h1 : term373 A f) : (term369 A f t') = True.
Proof. exact (TRANS (@lem4108729 A t' f h1) (@lem4108733 A)). Qed.
Lemma lem4108735 {A : Type'} (f : type686 A) (h1 : term373 A f) : (term371 A f) = (term536 A).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4108734 A t' f h1)). Qed.
Lemma lem4108736 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4108737 {A : Type'} (f : type686 A) (h1 : term373 A f) : (term373 A f) = (term537 A).
Proof. exact (MK_COMB (@lem4108736 A) (@lem4108735 A f h1)). Qed.
Lemma lem4108739 {A : Type'} (t : Prop) : (term538 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4108740 {A : Type'} (t : Prop) : (term539 A t) = t.
Proof. exact (@lem4108739 (A -> Prop) t). Qed.
Lemma lem4108741 {A : Type'} : (term537 A) = True.
Proof. exact (@lem4108740 A True). Qed.
Lemma lem4108742 {A : Type'} (f : type686 A) (h1 : term373 A f) : (term373 A f) = True.
Proof. exact (TRANS (@lem4108737 A f h1) (@lem4108741 A)). Qed.
Lemma lem4108743 {A : Type'} (f : type686 A) (h1 : term373 A f) (h2 : term355 A f) : (term540 A f) = (True /\ True).
Proof. exact (MK_COMB (@lem4108714 A f h2) (@lem4108742 A f h1)). Qed.
Lemma lem4108745 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4108746 : (True /\ True) = True.
Proof. exact (@lem4108745 True). Qed.
Lemma lem4108747 {A : Type'} (f : type686 A) (h1 : term373 A f) (h2 : term355 A f) : (term540 A f) = True.
Proof. exact (TRANS (@lem4108743 A f h1 h2) (@lem4108746)). Qed.
Lemma lem4108748 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term373 A f) (h2 : term355 A f) (h3 : term525 A s f) : (term541 A s f) = (True /\ True).
Proof. exact (MK_COMB (@lem4108703 A s f h3) (@lem4108747 A f h1 h2)). Qed.
Lemma lem4108750 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4108751 : (True /\ True) = True.
Proof. exact (@lem4108750 True). Qed.
Lemma lem4108752 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term373 A f) (h2 : term355 A f) (h3 : term525 A s f) : (term541 A s f) = True.
Proof. exact (TRANS (@lem4108748 A s f h1 h2 h3) (@lem4108751)). Qed.
Lemma lem4108753 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term373 A f) (h2 : @FINITE A s) (h3 : term355 A f) (h4 : term525 A s f) : (term5 A s f) = (True /\ True).
Proof. exact (MK_COMB (@lem4108697 A s h2) (@lem4108752 A s f h1 h3 h4)). Qed.
Lemma lem4108755 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4108756 : (True /\ True) = True.
Proof. exact (@lem4108755 True). Qed.
Lemma lem4108757 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term373 A f) (h2 : @FINITE A s) (h3 : term355 A f) (h4 : term525 A s f) : (term5 A s f) = True.
Proof. exact (TRANS (@lem4108753 A s f h1 h2 h3 h4) (@lem4108756)). Qed.
Lemma lem4108758 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term373 A f) (h2 : @FINITE A s) (h3 : term355 A f) (h4 : term525 A s f) : True = (term5 A s f).
Proof. exact (SYM (@lem4108757 A s f h1 h2 h3 h4)). Qed.
Lemma lem4108759 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term373 A f) (h2 : @FINITE A s) (h3 : term355 A f) (h4 : term525 A s f) : term5 A s f.
Proof. exact (EQ_MP (@lem4108758 A s f h1 h2 h3 h4) (@lem0)). Qed.
Lemma lem4108760 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term373 A f) (h2 : @FINITE A s) (h3 : term355 A f) (h4 : term525 A s f) : term6 A f s.
Proof. exact (@lem4108666 A f s (@lem4108759 A s f h1 h2 h3 h4)). Qed.
Lemma lem4108761 {A : Type'} (n : nat) (s : A -> Prop) (f : type686 A) (h1 : term373 A f) (h2 : @FINITE A s) (h3 : term355 A f) (h4 : (@CARD A s) = (S n)) (h5 : term525 A s f) : term523 A f s n.
Proof. exact (EQ_MP (@lem4108663 A f s n h2 h4) (@lem4108760 A s f h1 h2 h3 h5)). Qed.
Lemma lem4108762 {A : Type'} (f : type686 A) (s : A -> Prop) (n : nat) (h1 : term517 A f s n) : term515 A s n.
Proof. exact (proj2 (@lem4108584 A f s n h1)). Qed.
Lemma lem4108763 {A : Type'} (f : type686 A) (s : A -> Prop) (n : nat) (h1 : term517 A f s n) : term525 A s f.
Proof. exact (proj1 (@lem4108584 A f s n h1)). Qed.
Lemma lem4108764 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term515 A s n) : (@CARD A s) = (S n).
Proof. exact (proj2 (@lem4108585 A s n h1)). Qed.
Lemma lem4108765 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term515 A s n) : @FINITE A s.
Proof. exact (proj1 (@lem4108585 A s n h1)). Qed.
Lemma lem4108766 {A : Type'} (n : nat) (s : A -> Prop) (f : type686 A) (h1 : term373 A f) (h2 : @FINITE A s) (h3 : term355 A f) (h4 : (@CARD A s) = (S n)) (h5 : term525 A s f) : ((@CARD A s) = (S n)) = (term523 A f s n).
Proof. exact (prop_ext (fun h6 : (@CARD A s) = (S n) => @lem4108761 A n s f h1 h2 h3 h4 h5) (fun h6 : term523 A f s n => @lem4108587 A s n h4)). Qed.
Lemma lem4108767 {A : Type'} (n : nat) (s : A -> Prop) (f : type686 A) (h1 : term373 A f) (h2 : @FINITE A s) (h3 : term355 A f) (h4 : (@CARD A s) = (S n)) (h5 : term525 A s f) : term523 A f s n.
Proof. exact (EQ_MP (@lem4108766 A n s f h1 h2 h3 h4 h5) (@lem4108587 A s n h4)). Qed.
Lemma lem4108768 {A : Type'} (n : nat) (s : A -> Prop) (f : type686 A) (h1 : term373 A f) (h2 : @FINITE A s) (h3 : term355 A f) (h4 : (@CARD A s) = (S n)) (h5 : term525 A s f) : (@FINITE A s) = (term523 A f s n).
Proof. exact (prop_ext (fun h6 : @FINITE A s => @lem4108767 A n s f h1 h2 h3 h4 h5) (fun h6 : term523 A f s n => @lem4108588 A s h2)). Qed.
Lemma lem4108769 {A : Type'} (n : nat) (s : A -> Prop) (f : type686 A) (h1 : term373 A f) (h2 : @FINITE A s) (h3 : term355 A f) (h4 : (@CARD A s) = (S n)) (h5 : term525 A s f) : term523 A f s n.
Proof. exact (EQ_MP (@lem4108768 A n s f h1 h2 h3 h4 h5) (@lem4108588 A s h2)). Qed.
Lemma lem4108770 {A : Type'} (n : nat) (s : A -> Prop) (f : type686 A) (h1 : term373 A f) (h2 : @FINITE A s) (h3 : term355 A f) (h4 : term515 A s n) (h5 : term525 A s f) : ((@CARD A s) = (S n)) = (term523 A f s n).
Proof. exact (prop_ext (fun h6 : (@CARD A s) = (S n) => @lem4108769 A n s f h1 h2 h3 h6 h5) (fun h6 : term523 A f s n => @lem4108764 A s n h4)). Qed.
Lemma lem4108771 {A : Type'} (n : nat) (s : A -> Prop) (f : type686 A) (h1 : term373 A f) (h2 : @FINITE A s) (h3 : term355 A f) (h4 : term515 A s n) (h5 : term525 A s f) : term523 A f s n.
Proof. exact (EQ_MP (@lem4108770 A n s f h1 h2 h3 h4 h5) (@lem4108764 A s n h4)). Qed.
Lemma lem4108772 {A : Type'} (n : nat) (s : A -> Prop) (f : type686 A) (h1 : term373 A f) (h2 : term355 A f) (h3 : term515 A s n) (h4 : term525 A s f) : (@FINITE A s) = (term523 A f s n).
Proof. exact (prop_ext (fun h5 : @FINITE A s => @lem4108771 A n s f h1 h5 h2 h3 h4) (fun h5 : term523 A f s n => @lem4108765 A s n h3)). Qed.
Lemma lem4108773 {A : Type'} (n : nat) (s : A -> Prop) (f : type686 A) (h1 : term373 A f) (h2 : term355 A f) (h3 : term515 A s n) (h4 : term525 A s f) : term523 A f s n.
Proof. exact (EQ_MP (@lem4108772 A n s f h1 h2 h3 h4) (@lem4108765 A s n h3)). Qed.
Lemma lem4108774 {A : Type'} (n : nat) (s : A -> Prop) (f : type686 A) (h1 : term373 A f) (h2 : term355 A f) (h3 : term515 A s n) (h4 : term525 A s f) : (term525 A s f) = (term523 A f s n).
Proof. exact (prop_ext (fun h5 : term525 A s f => @lem4108773 A n s f h1 h2 h3 h4) (fun h5 : term523 A f s n => @lem4108586 A s f h4)). Qed.
Lemma lem4108775 {A : Type'} (n : nat) (s : A -> Prop) (f : type686 A) (h1 : term373 A f) (h2 : term355 A f) (h3 : term515 A s n) (h4 : term525 A s f) : term523 A f s n.
Proof. exact (EQ_MP (@lem4108774 A n s f h1 h2 h3 h4) (@lem4108586 A s f h4)). Qed.
Lemma lem4108776 {A : Type'} (n : nat) (s : A -> Prop) (f : type686 A) (h1 : term373 A f) (h2 : term355 A f) (h3 : term517 A f s n) (h4 : term525 A s f) : (term515 A s n) = (term523 A f s n).
Proof. exact (prop_ext (fun h5 : term515 A s n => @lem4108775 A n s f h1 h2 h5 h4) (fun h5 : term523 A f s n => @lem4108762 A f s n h3)). Qed.
Lemma lem4108777 {A : Type'} (n : nat) (s : A -> Prop) (f : type686 A) (h1 : term373 A f) (h2 : term355 A f) (h3 : term517 A f s n) (h4 : term525 A s f) : term523 A f s n.
Proof. exact (EQ_MP (@lem4108776 A n s f h1 h2 h3 h4) (@lem4108762 A f s n h3)). Qed.
Lemma lem4108778 {A : Type'} (f : type686 A) (s : A -> Prop) (n : nat) (h1 : term373 A f) (h2 : term355 A f) (h3 : term517 A f s n) : (term525 A s f) = (term523 A f s n).
Proof. exact (prop_ext (fun h4 : term525 A s f => @lem4108777 A n s f h1 h2 h3 h4) (fun h4 : term523 A f s n => @lem4108763 A f s n h3)). Qed.
Lemma lem4108779 {A : Type'} (f : type686 A) (s : A -> Prop) (n : nat) (h1 : term373 A f) (h2 : term355 A f) (h3 : term517 A f s n) : term523 A f s n.
Proof. exact (EQ_MP (@lem4108778 A f s n h1 h2 h3) (@lem4108763 A f s n h3)). Qed.
Lemma lem4108780 {A : Type'} (s : A -> Prop) (n : nat) (f : type686 A) (h1 : term373 A f) (h2 : term355 A f) : term524 A f s n.
Proof. exact (fun h0 : term517 A f s n => @lem4108779 A f s n h1 h2 h0). Qed.
Lemma lem4108781 {A : Type'} (s : A -> Prop) (n : nat) (f : type686 A) (h1 : term373 A f) (h2 : term355 A f) : term497 A f s n.
Proof. exact (EQ_MP (@lem4108583 A f s n) (@lem4108780 A s n f h1 h2)). Qed.
Lemma lem4108786 {A : Type'} (n : nat) (f : type686 A) (h1 : term373 A f) (h2 : term355 A f) : term501 A f n.
Proof. exact (fun s : A -> Prop => @lem4108781 A s n f h1 h2). Qed.
Lemma lem4108787 {A : Type'} (n : nat) (f : type686 A) (h1 : term373 A f) (h2 : term355 A f) : term487 A f n.
Proof. exact (@lem4108530 A f n (@lem4108786 A n f h1 h2)). Qed.
Lemma lem4108788 {A : Type'} (n : nat) (f : type686 A) (h1 : term373 A f) (h2 : term355 A f) : term466 A f n.
Proof. exact (EQ_MP (@lem4108489 A f n) (@lem4108787 A n f h1 h2)). Qed.
Lemma lem4108789 {A : Type'} (n : nat) (f : type686 A) (h1 : term373 A f) (h2 : term355 A f) : term447 A f n.
Proof. exact (EQ_MP (@lem4108448 A f n) (@lem4108788 A n f h1 h2)). Qed.
Lemma lem4108790 {A : Type'} (n : nat) (f : type686 A) (h1 : term373 A f) (h2 : term355 A f) : term440 A f n.
Proof. exact (EQ_MP (@lem4108396 A f n) (@lem4108789 A n f h1 h2)). Qed.
Lemma lem4108791 {A : Type'} (n : nat) (f : type686 A) (h1 : term373 A f) (h2 : term355 A f) : term427 A f n.
Proof. exact (EQ_MP (@lem4108351 A f n) (@lem4108790 A n f h1 h2)). Qed.
Lemma lem4108792 {A : Type'} (n : nat) (f : type686 A) (h1 : term373 A f) (h2 : term355 A f) : term400 A f n.
Proof. exact (EQ_MP (@lem4108308 A f n) (@lem4108791 A n f h1 h2)). Qed.
Lemma lem4108793 {A : Type'} (n : nat) (f : type686 A) (h1 : term373 A f) (h2 : term355 A f) : term399 A f n.
Proof. exact (EQ_MP (@lem4108248 A f n) (@lem4108792 A n f h1 h2)). Qed.
Lemma lem4108794 {A : Type'} (f : type686 A) (n : nat) (h1 : term386 A f n) : term384 A f n.
Proof. exact (proj2 (@lem4108242 A f n h1)). Qed.
Lemma lem4108795 {A : Type'} (f : type686 A) (n : nat) (h1 : term386 A f n) : term373 A f.
Proof. exact (proj1 (@lem4108242 A f n h1)). Qed.
Lemma lem4108796 {A : Type'} (n : nat) (f : type686 A) (h1 : term373 A f) (h2 : term384 A f n) (h3 : term355 A f) : term396 A f n.
Proof. exact (@lem4108793 A n f h1 h3 (@lem4108243 A f n h2)). Qed.
Lemma lem4108797 {A : Type'} (n : nat) (f : type686 A) (h1 : term373 A f) (h2 : term384 A f n) (h3 : term355 A f) : (term373 A f) = (term396 A f n).
Proof. exact (prop_ext (fun h4 : term373 A f => @lem4108796 A n f h1 h2 h3) (fun h4 : term396 A f n => @lem4108244 A f h1)). Qed.
Lemma lem4108798 {A : Type'} (n : nat) (f : type686 A) (h1 : term373 A f) (h2 : term384 A f n) (h3 : term355 A f) : term396 A f n.
Proof. exact (EQ_MP (@lem4108797 A n f h1 h2 h3) (@lem4108244 A f h1)). Qed.
Lemma lem4108799 {A : Type'} (f : type686 A) (n : nat) (h1 : term373 A f) (h2 : term355 A f) (h3 : term386 A f n) : (term384 A f n) = (term396 A f n).
Proof. exact (prop_ext (fun h4 : term384 A f n => @lem4108798 A n f h1 h4 h2) (fun h4 : term396 A f n => @lem4108794 A f n h3)). Qed.
Lemma lem4108800 {A : Type'} (f : type686 A) (n : nat) (h1 : term373 A f) (h2 : term355 A f) (h3 : term386 A f n) : term396 A f n.
Proof. exact (EQ_MP (@lem4108799 A f n h1 h2 h3) (@lem4108794 A f n h3)). Qed.
Lemma lem4108801 {A : Type'} (f : type686 A) (n : nat) (h1 : term355 A f) (h2 : term386 A f n) : (term373 A f) = (term396 A f n).
Proof. exact (prop_ext (fun h3 : term373 A f => @lem4108800 A f n h3 h1 h2) (fun h3 : term396 A f n => @lem4108795 A f n h2)). Qed.
Lemma lem4108802 {A : Type'} (f : type686 A) (n : nat) (h1 : term355 A f) (h2 : term386 A f n) : term396 A f n.
Proof. exact (EQ_MP (@lem4108801 A f n h1 h2) (@lem4108795 A f n h2)). Qed.
Lemma lem4108804 {A : Type'} (n : nat) (f : type686 A) (h1 : term355 A f) : term397 A f n.
Proof. exact (fun h0 : term386 A f n => @lem4108802 A f n h1 h0). Qed.
Lemma lem4108805 {A : Type'} (f : type686 A) (n : nat) : term397 A f n.
Proof. exact (or_elim (@lem4108029 A f) (fun h0 : f = (@EMPTY (A -> Prop)) => @lem4108181 A n f h0) (fun h0 : term355 A f => @lem4108804 A n f h0)). Qed.
Lemma lem4108810 {A : Type'} (f : type686 A) : term542 A f.
Proof. exact (fun n : nat => @lem4108805 A f n). Qed.
Lemma lem4108815 {A : Type'} : term543 A.
Proof. exact (fun f : type686 A => @lem4108810 A f). Qed.
