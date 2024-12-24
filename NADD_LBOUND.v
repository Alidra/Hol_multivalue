Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_LBOUND_term_abbrevs.
Require Import ARITH_SUC_spec.
Require Import LE_ADD_LCANCEL_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import LE_TRANS_spec.
Require Import MULT_CLAUSES_spec.
Require Import NADD_ARCH_MULT_spec.
Require Import NADD_MUL_spec.
Require Import NADD_NONZERO_spec.
Require Import NADD_OF_NUM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_LT_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import nadd_le_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm89994_spec.
Lemma lem1299988 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.le n m)) : (term0 m n) = (Peano.le n m).
Proof. exact (h1). Qed.
Lemma lem1299989 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.le n m)) : (Peano.le n m) = (term0 m n).
Proof. exact (SYM (@lem1299988 n m h1)). Qed.
Lemma lem1299990 (m : nat) (n : nat) (h1 : (Peano.le n m) = (term0 m n)) : (Peano.le n m) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem1299991 (m : nat) (n : nat) (h1 : (Peano.le n m) = (term0 m n)) : (term0 m n) = (Peano.le n m).
Proof. exact (SYM (@lem1299990 m n h1)). Qed.
Lemma lem1299992 (m : nat) (n : nat) : ((term0 m n) = (Peano.le n m)) = ((Peano.le n m) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.le n m) => @lem1299989 n m h1) (fun h1 : (Peano.le n m) = (term0 m n) => @lem1299991 m n h1)). Qed.
Lemma lem1299993 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem1299992 m n)). Qed.
Lemma lem1299994 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1299995 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem1299994) (@lem1299993 m)). Qed.
Lemma lem1299996 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem1299995 m)). Qed.
Lemma lem1299997 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1299998 : term7 = term8.
Proof. exact (MK_COMB (@lem1299997) (@lem1299996)). Qed.
Lemma lem1299999 : term8.
Proof. exact (EQ_MP (@lem1299998) (@lem98377)). Qed.
Lemma lem1300000 : term9.
Proof. exact (proj2 (@lem513080)). Qed.
Lemma lem1300011 : term10.
Proof. exact (proj1 (@lem513080)). Qed.
Lemma lem1300012 (n : nat) : term11 n.
Proof. exact (@lem1300011 n). Qed.
Lemma lem1300013 (n : nat) : (term11 n) = ((term12 n) = (term13 n)).
Proof. exact (eq_refl (term11 n)). Qed.
Lemma lem1300016 (n : nat) : (term12 n) = (term13 n).
Proof. exact (EQ_MP (@lem1300013 n) (@lem1300012 n)). Qed.
Lemma lem1300017 : term14 = term15.
Proof. exact (@lem1300016 0). Qed.
Lemma lem1300019 : (S 0) = (BIT1 0).
Proof. exact (proj1 (@lem1300000)). Qed.
Lemma lem1300020 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem1300021 : term15 = term16.
Proof. exact (MK_COMB (@lem1300020) (@lem1300019)). Qed.
Lemma lem1300022 : term14 = term16.
Proof. exact (TRANS (@lem1300017) (@lem1300021)). Qed.
Lemma lem1300023 (h1 : term14 = term16) : term14 = term16.
Proof. exact (h1). Qed.
Lemma lem1300024 (h1 : term14 = term16) : term16 = term14.
Proof. exact (SYM (@lem1300023 h1)). Qed.
Lemma lem1300025 (h1 : term16 = term14) : term16 = term14.
Proof. exact (h1). Qed.
Lemma lem1300026 (h1 : term16 = term14) : term14 = term16.
Proof. exact (SYM (@lem1300025 h1)). Qed.
Lemma lem1300027 : (term14 = term16) = (term16 = term14).
Proof. exact (prop_ext (fun h1 : term14 = term16 => @lem1300024 h1) (fun h1 : term16 = term14 => @lem1300026 h1)). Qed.
Lemma lem1300029 (m : nat) : term17 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem1300030 (m : nat) : (term17 m) = (term18 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem1300031 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem1300030 m) (@lem1300029 m)). Qed.
Lemma lem1300032 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem1300031 m n). Qed.
Lemma lem1300033 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem1300034 (m : nat) (n : nat) : term20 m n.
Proof. exact (EQ_MP (@lem1300033 m n) (@lem1300032 m n)). Qed.
Lemma lem1300035 (m : nat) (n : nat) (p : nat) : term21 m n p.
Proof. exact (@lem1300034 m n p). Qed.
Lemma lem1300036 (m : nat) (n : nat) (p : nat) : (term21 m n p) = ((term22 n m p) = (term23 m n p)).
Proof. exact (eq_refl (term21 m n p)). Qed.
Lemma lem1300038 : term24.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1300040 : term25.
Proof. exact (proj2 (@lem1300038)). Qed.
Lemma lem1300042 : term26.
Proof. exact (proj2 (@lem1300040)). Qed.
Lemma lem1300045 : term27.
Proof. exact (proj1 (@lem1300042)). Qed.
Lemma lem1300049 (m : nat) (h1 : (term28 m) = m) : (term28 m) = m.
Proof. exact (h1). Qed.
Lemma lem1300050 (m : nat) (h1 : (term28 m) = m) : m = (term28 m).
Proof. exact (SYM (@lem1300049 m h1)). Qed.
Lemma lem1300051 (m : nat) (h1 : m = (term28 m)) : m = (term28 m).
Proof. exact (h1). Qed.
Lemma lem1300052 (m : nat) (h1 : m = (term28 m)) : (term28 m) = m.
Proof. exact (SYM (@lem1300051 m h1)). Qed.
Lemma lem1300053 (m : nat) : ((term28 m) = m) = (m = (term28 m)).
Proof. exact (prop_ext (fun h1 : (term28 m) = m => @lem1300050 m h1) (fun h1 : m = (term28 m) => @lem1300052 m h1)). Qed.
Lemma lem1300054 : term29 = term30.
Proof. exact (fun_ext (fun m : nat => @lem1300053 m)). Qed.
Lemma lem1300055 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1300056 : term27 = term31.
Proof. exact (MK_COMB (@lem1300055) (@lem1300054)). Qed.
Lemma lem1300057 : term31.
Proof. exact (EQ_MP (@lem1300056) (@lem1300045)). Qed.
Lemma lem1300058 (m : nat) : term32 m.
Proof. exact (@lem1300057 m). Qed.
Lemma lem1300059 (m : nat) : (term32 m) = (m = (term28 m)).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem1300061 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem1300062 (m : nat) (h1 : term33) : term34 m.
Proof. exact (@lem1300061 h1 m). Qed.
Lemma lem1300063 (m : nat) : (term34 m) = (term35 m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem1300064 (m : nat) (h1 : term33) : term35 m.
Proof. exact (EQ_MP (@lem1300063 m) (@lem1300062 m h1)). Qed.
Lemma lem1300065 (m : nat) (n : nat) (h1 : term33) : term36 m n.
Proof. exact (@lem1300064 m h1 n). Qed.
Lemma lem1300066 (n : nat) (m : nat) : (term36 m n) = (term37 n m).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem1300067 (n : nat) (m : nat) (h1 : term33) : term37 n m.
Proof. exact (EQ_MP (@lem1300066 n m) (@lem1300065 m n h1)). Qed.
Lemma lem1300068 (n : nat) (m : nat) (p : nat) (h1 : term33) : term38 n m p.
Proof. exact (@lem1300067 n m h1 p). Qed.
Lemma lem1300069 (n : nat) (m : nat) (p : nat) : (term38 n m p) = (term39 n m p).
Proof. exact (eq_refl (term38 n m p)). Qed.
Lemma lem1300070 (n : nat) (m : nat) (p : nat) (h1 : term33) : term39 n m p.
Proof. exact (EQ_MP (@lem1300069 n m p) (@lem1300068 n m p h1)). Qed.
Lemma lem1300071 (m : nat) (n : nat) (p : nat) (h1 : term40 m n p) : term40 m n p.
Proof. exact (h1). Qed.
Lemma lem1300072 (m : nat) (n : nat) (p : nat) (h1 : term33) (h2 : term40 m n p) : Peano.le m p.
Proof. exact (@lem1300070 n m p h1 (@lem1300071 m n p h2)). Qed.
Lemma lem1300073 (m : nat) (n : nat) (p : nat) (h1 : term40 m n p) : term41 m p.
Proof. exact (fun h0 : term33 => @lem1300072 m n p h0 h1). Qed.
Lemma lem1300074 (m : nat) (p : nat) (h1 : term42 m p) : term42 m p.
Proof. exact (h1). Qed.
Lemma lem1300075 (m : nat) (p : nat) (h1 : term42 m p) : term41 m p.
Proof. exact (ex_elim (@lem1300074 m p h1) (fun n : nat => fun h0 : term43 m p n => @lem1300073 m n p h0)). Qed.
Lemma lem1300076 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem1300077 (m : nat) (p : nat) (h1 : term33) (h2 : term42 m p) : Peano.le m p.
Proof. exact (@lem1300075 m p h2 (@lem1300076 h1)). Qed.
Lemma lem1300078 (m : nat) (p : nat) (h1 : term33) : term44 m p.
Proof. exact (fun h0 : term42 m p => @lem1300077 m p h1 h0). Qed.
Lemma lem1300079 (m : nat) (h1 : term33) : term45 m.
Proof. exact (fun p : nat => @lem1300078 m p h1). Qed.
Lemma lem1300080 (h1 : term33) : term46.
Proof. exact (fun m : nat => @lem1300079 m h1). Qed.
Lemma lem1300081 : term47.
Proof. exact (fun h0 : term33 => @lem1300080 h0). Qed.
Lemma lem1300082 : term46.
Proof. exact (@lem1300081 (@lem93743)). Qed.
Lemma lem1300083 (m : nat) : term48 m.
Proof. exact (@lem1300082 m). Qed.
Lemma lem1300084 (m : nat) : (term48 m) = (term45 m).
Proof. exact (eq_refl (term48 m)). Qed.
Lemma lem1300085 (m : nat) : term45 m.
Proof. exact (EQ_MP (@lem1300084 m) (@lem1300083 m)). Qed.
Lemma lem1300086 (m : nat) (p : nat) : term49 m p.
Proof. exact (@lem1300085 m p). Qed.
Lemma lem1300087 (m : nat) (p : nat) : (term49 m p) = (term44 m p).
Proof. exact (eq_refl (term49 m p)). Qed.
Lemma lem1300089 : term24.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1300090 : term25.
Proof. exact (proj2 (@lem1300089)). Qed.
Lemma lem1300111 : term50.
Proof. exact (proj1 (@lem1300090)). Qed.
Lemma lem1300112 (n : nat) : term51 n.
Proof. exact (@lem1300111 n). Qed.
Lemma lem1300113 (n : nat) : (term51 n) = ((term52 n) = n).
Proof. exact (eq_refl (term51 n)). Qed.
Lemma lem1300123 (k : nat) : term53 k.
Proof. exact (@lem1268972 k). Qed.
Lemma lem1300124 (k : nat) : (term53 k) = ((term54 k) = (term55 k)).
Proof. exact (eq_refl (term53 k)). Qed.
Lemma lem1300126 (x : nadd) : term56 x.
Proof. exact (@lem1277879 x). Qed.
Lemma lem1300127 (x : nadd) : (term56 x) = (term57 x).
Proof. exact (eq_refl (term56 x)). Qed.
Lemma lem1300128 (x : nadd) : term57 x.
Proof. exact (EQ_MP (@lem1300127 x) (@lem1300126 x)). Qed.
Lemma lem1300129 (x : nadd) (y : nadd) : term58 x y.
Proof. exact (@lem1300128 x y). Qed.
Lemma lem1300130 (x : nadd) (y : nadd) : (term58 x y) = ((term59 x y) = (term60 x y)).
Proof. exact (eq_refl (term58 x y)). Qed.
Lemma lem1300132 (x : nadd) : term61 x.
Proof. exact (@lem1269692 x). Qed.
Lemma lem1300133 (x : nadd) : (term61 x) = (term62 x).
Proof. exact (eq_refl (term61 x)). Qed.
Lemma lem1300134 (x : nadd) : term62 x.
Proof. exact (EQ_MP (@lem1300133 x) (@lem1300132 x)). Qed.
Lemma lem1300135 (x : nadd) (y : nadd) : term63 x y.
Proof. exact (@lem1300134 x y). Qed.
Lemma lem1300136 (x : nadd) (y : nadd) : (term63 x y) = ((nadd_le x y) = (term64 x y)).
Proof. exact (eq_refl (term63 x y)). Qed.
Lemma lem1300138 (h1 : term65) : term65.
Proof. exact (h1). Qed.
Lemma lem1300139 (x : nadd) (h1 : term65) : term66 x.
Proof. exact (@lem1300138 h1 x). Qed.
Lemma lem1300140 (x : nadd) : (term66 x) = (term67 x).
Proof. exact (eq_refl (term66 x)). Qed.
Lemma lem1300141 (x : nadd) (h1 : term65) : term67 x.
Proof. exact (EQ_MP (@lem1300140 x) (@lem1300139 x h1)). Qed.
Lemma lem1300142 (x : nadd) (k : nat) (h1 : term65) : term68 x k.
Proof. exact (@lem1300141 x h1 k). Qed.
Lemma lem1300143 (k : nat) (x : nadd) : (term68 x k) = (term69 k x).
Proof. exact (eq_refl (term68 x k)). Qed.
Lemma lem1300144 (k : nat) (x : nadd) (h1 : term65) : term69 k x.
Proof. exact (EQ_MP (@lem1300143 k x) (@lem1300142 x k h1)). Qed.
Lemma lem1300145 (x : nadd) (h1 : term70 x) : term70 x.
Proof. exact (h1). Qed.
Lemma lem1300146 (k : nat) (x : nadd) (h1 : term65) (h2 : term70 x) : term71 k x.
Proof. exact (@lem1300144 k x h1 (@lem1300145 x h2)). Qed.
Lemma lem1300147 (x : nadd) (h1 : term65) (h2 : term70 x) : term72 x.
Proof. exact (fun k : nat => @lem1300146 k x h1 h2). Qed.
Lemma lem1300148 (x : nadd) (h1 : term65) : term73 x.
Proof. exact (fun h0 : term70 x => @lem1300147 x h1 h0). Qed.
Lemma lem1300149 (h1 : term65) : term74.
Proof. exact (fun x : nadd => @lem1300148 x h1). Qed.
Lemma lem1300150 : term75.
Proof. exact (fun h0 : term65 => @lem1300149 h0). Qed.
Lemma lem1300151 : term74.
Proof. exact (@lem1300150 (@lem1286557)). Qed.
Lemma lem1300152 (x : nadd) : term76 x.
Proof. exact (@lem1300151 x). Qed.
Lemma lem1300153 (x : nadd) : (term76 x) = (term73 x).
Proof. exact (eq_refl (term76 x)). Qed.
Lemma lem1300155 (x : nadd) : term77 x.
Proof. exact (@lem1299985 x). Qed.
Lemma lem1300156 (x : nadd) : (term77 x) = (term78 x).
Proof. exact (eq_refl (term77 x)). Qed.
Lemma lem1300158 (x : nadd) (h1 : term70 x) : term70 x.
Proof. exact (h1). Qed.
Lemma lem1300160 (x : nadd) : term78 x.
Proof. exact (EQ_MP (@lem1300156 x) (@lem1300155 x)). Qed.
Lemma lem1300161 (x : nadd) (h1 : term70 x) : term79 x.
Proof. exact (@lem1300160 x (@lem1300158 x h1)). Qed.
Lemma lem1300162 (N : nat) (x : nadd) (h1 : term80 N x) : term80 N x.
Proof. exact (h1). Qed.
Lemma lem1300166 (x : nadd) : term73 x.
Proof. exact (EQ_MP (@lem1300153 x) (@lem1300152 x)). Qed.
Lemma lem1300167 (x : nadd) (h1 : term70 x) : term72 x.
Proof. exact (@lem1300166 x (@lem1300158 x h1)). Qed.
Lemma lem1300168 (x : nadd) (h1 : term72 x) : term72 x.
Proof. exact (h1). Qed.
Lemma lem1300169 (x : nadd) (h1 : term72 x) : term81 x.
Proof. exact (@lem1300168 x h1 term16). Qed.
Lemma lem1300170 (x : nadd) : (term81 x) = (term82 x).
Proof. exact (eq_refl (term81 x)). Qed.
Lemma lem1300171 (x : nadd) (h1 : term72 x) : term82 x.
Proof. exact (EQ_MP (@lem1300170 x) (@lem1300169 x h1)). Qed.
Lemma lem1300179 (x : nadd) (y : nadd) : (nadd_le x y) = (term64 x y).
Proof. exact (EQ_MP (@lem1300136 x y) (@lem1300135 x y)). Qed.
Lemma lem1300180 (N : nat) (x : nadd) : (term83 N x) = (term84 N x).
Proof. exact (@lem1300179 term85 (term86 N x)). Qed.
Lemma lem1300190 (k : nat) : (term54 k) = (term55 k).
Proof. exact (EQ_MP (@lem1300124 k) (@lem1300123 k)). Qed.
Lemma lem1300191 : term87 = term88.
Proof. exact (@lem1300190 term16). Qed.
Lemma lem1300193 (n : nat) : (term52 n) = n.
Proof. exact (EQ_MP (@lem1300113 n) (@lem1300112 n)). Qed.
Lemma lem1300194 : term88 = term89.
Proof. exact (fun_ext (fun n : nat => @lem1300193 n)). Qed.
Lemma lem1300195 : term87 = term89.
Proof. exact (TRANS (@lem1300191) (@lem1300194)). Qed.
Lemma lem1300196 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1300197 (n : nat) : (term90 n) = (term91 n).
Proof. exact (MK_COMB (@lem1300195) (@lem1300196 n)). Qed.
Lemma lem1300199 {A B : Type'} (f : A -> B) (y : A) : (term92 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1300200 (f : nat -> nat) (y : nat) : (term93 f y) = (f y).
Proof. exact (@lem1300199 nat nat f y). Qed.
Lemma lem1300201 (n : nat) : (term94 n) = (term91 n).
Proof. exact (@lem1300200 term89 n). Qed.
Lemma lem1300202 (n : nat) : (term91 n) = n.
Proof. exact (eq_refl (term91 n)). Qed.
Lemma lem1300203 : term95 = term89.
Proof. exact (fun_ext (fun n : nat => @lem1300202 n)). Qed.
Lemma lem1300204 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1300205 (n : nat) : (term94 n) = (term91 n).
Proof. exact (MK_COMB (@lem1300203) (@lem1300204 n)). Qed.
Lemma lem1300206 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1300207 (n : nat) : (term96 n) = (term97 n).
Proof. exact (MK_COMB (@lem1300206) (@lem1300205 n)). Qed.
Lemma lem1300208 (n : nat) : (term91 n) = n.
Proof. exact (eq_refl (term91 n)). Qed.
Lemma lem1300209 (n : nat) : ((term94 n) = (term91 n)) = ((term91 n) = n).
Proof. exact (MK_COMB (@lem1300207 n) (@lem1300208 n)). Qed.
Lemma lem1300210 (n : nat) : (term91 n) = n.
Proof. exact (EQ_MP (@lem1300209 n) (@lem1300201 n)). Qed.
Lemma lem1300211 (n : nat) : (term90 n) = n.
Proof. exact (TRANS (@lem1300197 n) (@lem1300210 n)). Qed.
Lemma lem1300212 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1300213 (n : nat) : (term98 n) = (Peano.le n).
Proof. exact (MK_COMB (@lem1300212) (@lem1300211 n)). Qed.
Lemma lem1300215 (x : nadd) (y : nadd) : (term59 x y) = (term60 x y).
Proof. exact (EQ_MP (@lem1300130 x y) (@lem1300129 x y)). Qed.
Lemma lem1300216 (N : nat) (x : nadd) : (term99 N x) = (term100 N x).
Proof. exact (@lem1300215 (nadd_of_num N) x). Qed.
Lemma lem1300218 (k : nat) : (term54 k) = (term55 k).
Proof. exact (EQ_MP (@lem1300124 k) (@lem1300123 k)). Qed.
Lemma lem1300219 (N : nat) : (term54 N) = (term55 N).
Proof. exact (@lem1300218 N). Qed.
Lemma lem1300220 (x : nadd) (n : nat) : (dest_nadd x n) = (dest_nadd x n).
Proof. exact (eq_refl (dest_nadd x n)). Qed.
Lemma lem1300221 (N : nat) (x : nadd) (n : nat) : (term101 N x n) = (term102 N x n).
Proof. exact (MK_COMB (@lem1300219 N) (@lem1300220 x n)). Qed.
Lemma lem1300223 {A B : Type'} (f : A -> B) (y : A) : (term92 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1300224 (f : nat -> nat) (y : nat) : (term93 f y) = (f y).
Proof. exact (@lem1300223 nat nat f y). Qed.
Lemma lem1300225 (N : nat) (x : nadd) (n : nat) : (term103 N x n) = (term102 N x n).
Proof. exact (@lem1300224 (term55 N) (dest_nadd x n)). Qed.
Lemma lem1300226 (N : nat) (n : nat) : (term104 N n) = (Nat.mul N n).
Proof. exact (eq_refl (term104 N n)). Qed.
Lemma lem1300227 (N : nat) : (term105 N) = (term55 N).
Proof. exact (fun_ext (fun n : nat => @lem1300226 N n)). Qed.
Lemma lem1300228 (x : nadd) (n : nat) : (dest_nadd x n) = (dest_nadd x n).
Proof. exact (eq_refl (dest_nadd x n)). Qed.
Lemma lem1300229 (N : nat) (x : nadd) (n : nat) : (term103 N x n) = (term102 N x n).
Proof. exact (MK_COMB (@lem1300227 N) (@lem1300228 x n)). Qed.
Lemma lem1300230 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1300231 (N : nat) (x : nadd) (n : nat) : (term106 N x n) = (term107 N x n).
Proof. exact (MK_COMB (@lem1300230) (@lem1300229 N x n)). Qed.
Lemma lem1300232 (N : nat) (x : nadd) (n : nat) : (term102 N x n) = (term108 N x n).
Proof. exact (eq_refl (term102 N x n)). Qed.
Lemma lem1300233 (N : nat) (x : nadd) (n : nat) : ((term103 N x n) = (term102 N x n)) = ((term102 N x n) = (term108 N x n)).
Proof. exact (MK_COMB (@lem1300231 N x n) (@lem1300232 N x n)). Qed.
Lemma lem1300234 (N : nat) (x : nadd) (n : nat) : (term102 N x n) = (term108 N x n).
Proof. exact (EQ_MP (@lem1300233 N x n) (@lem1300225 N x n)). Qed.
Lemma lem1300235 (N : nat) (x : nadd) (n : nat) : (term101 N x n) = (term108 N x n).
Proof. exact (TRANS (@lem1300221 N x n) (@lem1300234 N x n)). Qed.
Lemma lem1300236 (N : nat) (x : nadd) : (term100 N x) = (term109 N x).
Proof. exact (fun_ext (fun n : nat => @lem1300235 N x n)). Qed.
Lemma lem1300237 (N : nat) (x : nadd) : (term99 N x) = (term109 N x).
Proof. exact (TRANS (@lem1300216 N x) (@lem1300236 N x)). Qed.
Lemma lem1300238 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1300239 (N : nat) (x : nadd) (n : nat) : (term110 N x n) = (term111 N x n).
Proof. exact (MK_COMB (@lem1300237 N x) (@lem1300238 n)). Qed.
Lemma lem1300241 {A B : Type'} (f : A -> B) (y : A) : (term92 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1300242 (f : nat -> nat) (y : nat) : (term93 f y) = (f y).
Proof. exact (@lem1300241 nat nat f y). Qed.
Lemma lem1300243 (N : nat) (x : nadd) (n : nat) : (term112 N x n) = (term111 N x n).
Proof. exact (@lem1300242 (term109 N x) n). Qed.
Lemma lem1300244 (N : nat) (x : nadd) (n : nat) : (term111 N x n) = (term108 N x n).
Proof. exact (eq_refl (term111 N x n)). Qed.
Lemma lem1300245 (N : nat) (x : nadd) : (term113 N x) = (term109 N x).
Proof. exact (fun_ext (fun n : nat => @lem1300244 N x n)). Qed.
Lemma lem1300246 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1300247 (N : nat) (x : nadd) (n : nat) : (term112 N x n) = (term111 N x n).
Proof. exact (MK_COMB (@lem1300245 N x) (@lem1300246 n)). Qed.
Lemma lem1300248 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1300249 (N : nat) (x : nadd) (n : nat) : (term114 N x n) = (term115 N x n).
Proof. exact (MK_COMB (@lem1300248) (@lem1300247 N x n)). Qed.
Lemma lem1300250 (N : nat) (x : nadd) (n : nat) : (term111 N x n) = (term108 N x n).
Proof. exact (eq_refl (term111 N x n)). Qed.
Lemma lem1300251 (N : nat) (x : nadd) (n : nat) : ((term112 N x n) = (term111 N x n)) = ((term111 N x n) = (term108 N x n)).
Proof. exact (MK_COMB (@lem1300249 N x n) (@lem1300250 N x n)). Qed.
Lemma lem1300252 (N : nat) (x : nadd) (n : nat) : (term111 N x n) = (term108 N x n).
Proof. exact (EQ_MP (@lem1300251 N x n) (@lem1300243 N x n)). Qed.
Lemma lem1300253 (N : nat) (x : nadd) (n : nat) : (term110 N x n) = (term108 N x n).
Proof. exact (TRANS (@lem1300239 N x n) (@lem1300252 N x n)). Qed.
Lemma lem1300254 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1300255 (N : nat) (x : nadd) (n : nat) : (term116 N x n) = (term117 N x n).
Proof. exact (MK_COMB (@lem1300254) (@lem1300253 N x n)). Qed.
Lemma lem1300256 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1300257 (N : nat) (x : nadd) (n : nat) (B : nat) : (term118 N x n B) = (term119 N x n B).
Proof. exact (MK_COMB (@lem1300255 N x n) (@lem1300256 B)). Qed.
Lemma lem1300258 (N : nat) (x : nadd) (n : nat) (B : nat) : (term120 N x n B) = (term121 N x n B).
Proof. exact (MK_COMB (@lem1300213 n) (@lem1300257 N x n B)). Qed.
Lemma lem1300259 (N : nat) (x : nadd) (B : nat) : (term122 N x B) = (term123 N x B).
Proof. exact (fun_ext (fun n : nat => @lem1300258 N x n B)). Qed.
Lemma lem1300260 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1300261 (N : nat) (x : nadd) (B : nat) : (term124 N x B) = (term125 N x B).
Proof. exact (MK_COMB (@lem1300260) (@lem1300259 N x B)). Qed.
Lemma lem1300266 (N : nat) (x : nadd) : (term126 N x) = (term127 N x).
Proof. exact (fun_ext (fun B : nat => @lem1300261 N x B)). Qed.
Lemma lem1300267 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1300268 (N : nat) (x : nadd) : (term84 N x) = (term128 N x).
Proof. exact (MK_COMB (@lem1300267) (@lem1300266 N x)). Qed.
Lemma lem1300273 (N : nat) (x : nadd) : (term83 N x) = (term128 N x).
Proof. exact (TRANS (@lem1300180 N x) (@lem1300268 N x)). Qed.
Lemma lem1300274 (x : nadd) : (term129 x) = (term130 x).
Proof. exact (fun_ext (fun N : nat => @lem1300273 N x)). Qed.
Lemma lem1300275 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1300276 (x : nadd) : (term82 x) = (term131 x).
Proof. exact (MK_COMB (@lem1300275) (@lem1300274 x)). Qed.
Lemma lem1300281 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1300282 (x : nadd) : (term132 x) = (term133 x).
Proof. exact (MK_COMB (@lem1300281) (@lem1300276 x)). Qed.
Lemma lem1300297 (x : nadd) : (term134 x) = (term134 x).
Proof. exact (eq_refl (term134 x)). Qed.
Lemma lem1300298 (x : nadd) : (term135 x) = (term136 x).
Proof. exact (MK_COMB (@lem1300282 x) (@lem1300297 x)). Qed.
Lemma lem1300301 (x : nadd) : (term136 x) = (term135 x).
Proof. exact (SYM (@lem1300298 x)). Qed.
Lemma lem1300302 (x : nadd) (h1 : term131 x) : term131 x.
Proof. exact (h1). Qed.
Lemma lem1300303 (A1 : nat) (x : nadd) (h1 : term128 A1 x) : term128 A1 x.
Proof. exact (h1). Qed.
Lemma lem1300304 (A1 : nat) (x : nadd) (A2 : nat) (h1 : term125 A1 x A2) : term125 A1 x A2.
Proof. exact (h1). Qed.
Lemma lem1300305 (N : nat) (n : nat) (h1 : Peano.le N n) : Peano.le N n.
Proof. exact (h1). Qed.
Lemma lem1300306 (n : nat) (N : nat) (x : nadd) (h1 : term80 N x) : term137 N x n.
Proof. exact (@lem1300162 N x h1 n). Qed.
Lemma lem1300307 (N : nat) (x : nadd) (n : nat) : (term137 N x n) = (term138 N x n).
Proof. exact (eq_refl (term137 N x n)). Qed.
Lemma lem1300310 (n : nat) (N : nat) (x : nadd) (h1 : term80 N x) : term138 N x n.
Proof. exact (EQ_MP (@lem1300307 N x n) (@lem1300306 n N x h1)). Qed.
Lemma lem1300311 (x : nadd) (N : nat) (n : nat) (h1 : term80 N x) (h2 : Peano.le N n) : term139 x n.
Proof. exact (@lem1300310 n N x h1 (@lem1300305 N n h2)). Qed.
Lemma lem1300313 (m : nat) (p : nat) : term44 m p.
Proof. exact (EQ_MP (@lem1300087 m p) (@lem1300086 m p)). Qed.
Lemma lem1300314 (A1 : nat) (A2 : nat) (x : nadd) (n : nat) : term140 A1 A2 x n.
Proof. exact (@lem1300313 n (term141 A1 A2 x n)). Qed.
Lemma lem1300315 (m : nat) : term142 m.
Proof. exact (@lem100902 m). Qed.
Lemma lem1300316 (m : nat) : (term142 m) = (term143 m).
Proof. exact (eq_refl (term142 m)). Qed.
Lemma lem1300317 (m : nat) : term143 m.
Proof. exact (EQ_MP (@lem1300316 m) (@lem1300315 m)). Qed.
Lemma lem1300318 (m : nat) (n : nat) : term144 m n.
Proof. exact (@lem1300317 m n). Qed.
Lemma lem1300319 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (eq_refl (term144 m n)). Qed.
Lemma lem1300320 (m : nat) (n : nat) : term145 m n.
Proof. exact (EQ_MP (@lem1300319 m n) (@lem1300318 m n)). Qed.
Lemma lem1300321 (m : nat) (n : nat) (p : nat) : term146 m n p.
Proof. exact (@lem1300320 m n p). Qed.
Lemma lem1300322 (m : nat) (n : nat) (p : nat) : (term146 m n p) = ((term147 n m p) = (Peano.le n p)).
Proof. exact (eq_refl (term146 m n p)). Qed.
Lemma lem1300324 (m : nat) : term148 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1300325 (m : nat) : (term148 m) = (term149 m).
Proof. exact (eq_refl (term148 m)). Qed.
Lemma lem1300326 (m : nat) : term149 m.
Proof. exact (EQ_MP (@lem1300325 m) (@lem1300324 m)). Qed.
Lemma lem1300327 (m : nat) (n : nat) : term150 m n.
Proof. exact (@lem1300326 m n). Qed.
Lemma lem1300328 (m : nat) (n : nat) : (term150 m n) = (term151 m n).
Proof. exact (eq_refl (term150 m n)). Qed.
Lemma lem1300329 (m : nat) (n : nat) : term151 m n.
Proof. exact (EQ_MP (@lem1300328 m n) (@lem1300327 m n)). Qed.
Lemma lem1300330 (m : nat) (n : nat) (p : nat) : term152 m n p.
Proof. exact (@lem1300329 m n p). Qed.
Lemma lem1300331 (m : nat) (n : nat) (p : nat) : (term152 m n p) = ((term153 m n p) = (term154 m n p)).
Proof. exact (eq_refl (term152 m n p)). Qed.
Lemma lem1300340 (n : nat) (A1 : nat) (x : nadd) (A2 : nat) (h1 : term125 A1 x A2) : term155 A1 x A2 n.
Proof. exact (@lem1300304 A1 x A2 h1 n). Qed.
Lemma lem1300341 (A1 : nat) (x : nadd) (n : nat) (A2 : nat) : (term155 A1 x A2 n) = (term121 A1 x n A2).
Proof. exact (eq_refl (term155 A1 x A2 n)). Qed.
Lemma lem1300342 (n : nat) (A1 : nat) (x : nadd) (A2 : nat) (h1 : term125 A1 x A2) : term121 A1 x n A2.
Proof. exact (EQ_MP (@lem1300341 A1 x n A2) (@lem1300340 n A1 x A2 h1)). Qed.
Lemma lem1300343 (A1 : nat) (x : nadd) (n : nat) (A2 : nat) : (term121 A1 x n A2) = ((term121 A1 x n A2) = True).
Proof. exact (@lem7 (term121 A1 x n A2)). Qed.
Lemma lem1300361 (n : nat) (A1 : nat) (x : nadd) (A2 : nat) (h1 : term125 A1 x A2) : (term121 A1 x n A2) = True.
Proof. exact (EQ_MP (@lem1300343 A1 x n A2) (@lem1300342 n A1 x A2 h1)). Qed.
Lemma lem1300362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1300363 (n : nat) (A1 : nat) (x : nadd) (A2 : nat) (h1 : term125 A1 x A2) : (term156 A1 x n A2) = (and True).
Proof. exact (MK_COMB (@lem1300362) (@lem1300361 n A1 x A2 h1)). Qed.
Lemma lem1300365 (m : nat) (n : nat) (p : nat) : (term153 m n p) = (term154 m n p).
Proof. exact (EQ_MP (@lem1300331 m n p) (@lem1300330 m n p)). Qed.
Lemma lem1300366 (A1 : nat) (A2 : nat) (x : nadd) (n : nat) : (term141 A1 A2 x n) = (term157 A1 A2 x n).
Proof. exact (@lem1300365 A1 A2 (dest_nadd x n)). Qed.
Lemma lem1300367 (A1 : nat) (x : nadd) (n : nat) (A2 : nat) : (term158 A1 x n A2) = (term158 A1 x n A2).
Proof. exact (eq_refl (term158 A1 x n A2)). Qed.
Lemma lem1300368 (A1 : nat) (A2 : nat) (x : nadd) (n : nat) : (term159 A1 A2 x n) = (term160 A1 A2 x n).
Proof. exact (MK_COMB (@lem1300367 A1 x n A2) (@lem1300366 A1 A2 x n)). Qed.
Lemma lem1300370 (m : nat) (n : nat) (p : nat) : (term147 n m p) = (Peano.le n p).
Proof. exact (EQ_MP (@lem1300322 m n p) (@lem1300321 m n p)). Qed.
Lemma lem1300371 (A1 : nat) (A2 : nat) (x : nadd) (n : nat) : (term160 A1 A2 x n) = (term161 A2 x n).
Proof. exact (@lem1300370 (term108 A1 x n) A2 (term108 A2 x n)). Qed.
Lemma lem1300372 (A1 : nat) (A2 : nat) (x : nadd) (n : nat) : (term159 A1 A2 x n) = (term161 A2 x n).
Proof. exact (TRANS (@lem1300368 A1 A2 x n) (@lem1300371 A1 A2 x n)). Qed.
Lemma lem1300373 (n : nat) (A1 : nat) (x : nadd) (A2 : nat) (h1 : term125 A1 x A2) : (term162 A1 A2 x n) = (term163 A2 x n).
Proof. exact (MK_COMB (@lem1300363 n A1 x A2 h1) (@lem1300372 A1 A2 x n)). Qed.
Lemma lem1300375 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1300376 (A2 : nat) (x : nadd) (n : nat) : (term163 A2 x n) = (term161 A2 x n).
Proof. exact (@lem1300375 (term161 A2 x n)). Qed.
Lemma lem1300377 (n : nat) (A1 : nat) (x : nadd) (A2 : nat) (h1 : term125 A1 x A2) : (term162 A1 A2 x n) = (term161 A2 x n).
Proof. exact (TRANS (@lem1300373 n A1 x A2 h1) (@lem1300376 A2 x n)). Qed.
Lemma lem1300378 (n : nat) (A1 : nat) (x : nadd) (A2 : nat) (h1 : term125 A1 x A2) : (term161 A2 x n) = (term162 A1 A2 x n).
Proof. exact (SYM (@lem1300377 n A1 x A2 h1)). Qed.
Lemma lem1300380 (m : nat) : m = (term28 m).
Proof. exact (EQ_MP (@lem1300059 m) (@lem1300058 m)). Qed.
Lemma lem1300381 (A2 : nat) : A2 = (term28 A2).
Proof. exact (@lem1300380 A2). Qed.
Lemma lem1300382 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1300383 (A2 : nat) : (Peano.le A2) = (term164 A2).
Proof. exact (MK_COMB (@lem1300382) (@lem1300381 A2)). Qed.
Lemma lem1300384 (A2 : nat) (x : nadd) (n : nat) : (term108 A2 x n) = (term108 A2 x n).
Proof. exact (eq_refl (term108 A2 x n)). Qed.
Lemma lem1300385 (A2 : nat) (x : nadd) (n : nat) : (term161 A2 x n) = (term165 A2 x n).
Proof. exact (MK_COMB (@lem1300383 A2) (@lem1300384 A2 x n)). Qed.
Lemma lem1300386 (A2 : nat) (x : nadd) (n : nat) : (term165 A2 x n) = (term161 A2 x n).
Proof. exact (SYM (@lem1300385 A2 x n)). Qed.
Lemma lem1300388 (m : nat) (n : nat) (p : nat) : (term22 n m p) = (term23 m n p).
Proof. exact (EQ_MP (@lem1300036 m n p) (@lem1300035 m n p)). Qed.
Lemma lem1300389 (A2 : nat) (x : nadd) (n : nat) : (term165 A2 x n) = (term166 A2 x n).
Proof. exact (@lem1300388 A2 term16 (dest_nadd x n)). Qed.
Lemma lem1300394 (A2 : nat) (x : nadd) (n : nat) : (term166 A2 x n) = (term165 A2 x n).
Proof. exact (SYM (@lem1300389 A2 x n)). Qed.
Lemma lem1300396 : term16 = term14.
Proof. exact (EQ_MP (@lem1300027) (@lem1300022)). Qed.
Lemma lem1300397 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1300398 : term167 = term168.
Proof. exact (MK_COMB (@lem1300397) (@lem1300396)). Qed.
Lemma lem1300399 (x : nadd) (n : nat) : (dest_nadd x n) = (dest_nadd x n).
Proof. exact (eq_refl (dest_nadd x n)). Qed.
Lemma lem1300400 (x : nadd) (n : nat) : (term169 x n) = (term170 x n).
Proof. exact (MK_COMB (@lem1300398) (@lem1300399 x n)). Qed.
Lemma lem1300401 (x : nadd) (n : nat) : (term170 x n) = (term169 x n).
Proof. exact (SYM (@lem1300400 x n)). Qed.
Lemma lem1300402 : term171.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem1300403 (m : nat) : term172 m.
Proof. exact (@lem1300402 m). Qed.
Lemma lem1300404 (m : nat) : (term172 m) = (term173 m).
Proof. exact (eq_refl (term172 m)). Qed.
Lemma lem1300405 (m : nat) : term173 m.
Proof. exact (EQ_MP (@lem1300404 m) (@lem1300403 m)). Qed.
Lemma lem1300406 (m : nat) (n : nat) : term174 m n.
Proof. exact (@lem1300405 m n). Qed.
Lemma lem1300407 (m : nat) (n : nat) : (term174 m n) = ((term175 m n) = (term176 m n)).
Proof. exact (eq_refl (term174 m n)). Qed.
Lemma lem1300409 : term177.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem1300410 (m : nat) : term178 m.
Proof. exact (@lem1300409 m). Qed.
Lemma lem1300411 (m : nat) : (term178 m) = ((term179 m) = False).
Proof. exact (eq_refl (term178 m)). Qed.
Lemma lem1300413 (m : nat) : term180 m.
Proof. exact (@lem1299999 m). Qed.
Lemma lem1300414 (m : nat) : (term180 m) = (term4 m).
Proof. exact (eq_refl (term180 m)). Qed.
Lemma lem1300415 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem1300414 m) (@lem1300413 m)). Qed.
Lemma lem1300416 (m : nat) (n : nat) : term181 m n.
Proof. exact (@lem1300415 m n). Qed.
Lemma lem1300417 (m : nat) (n : nat) : (term181 m n) = ((Peano.le n m) = (term0 m n)).
Proof. exact (eq_refl (term181 m n)). Qed.
Lemma lem1300431 (x : nadd) (n : nat) : term182 x n.
Proof. exact (@lem82 ((dest_nadd x n) = (NUMERAL 0))). Qed.
Lemma lem1300445 (m : nat) (n : nat) : (Peano.le n m) = (term0 m n).
Proof. exact (EQ_MP (@lem1300417 m n) (@lem1300416 m n)). Qed.
Lemma lem1300446 (x : nadd) (n : nat) : (term170 x n) = (term183 x n).
Proof. exact (@lem1300445 (dest_nadd x n) term14). Qed.
Lemma lem1300448 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (EQ_MP (@lem1300407 m n) (@lem1300406 m n)). Qed.
Lemma lem1300449 (x : nadd) (n : nat) : (term184 x n) = (term185 x n).
Proof. exact (@lem1300448 (dest_nadd x n) (NUMERAL 0)). Qed.
Lemma lem1300453 (x : nadd) (N : nat) (n : nat) (h1 : term80 N x) (h2 : Peano.le N n) : ((dest_nadd x n) = (NUMERAL 0)) = False.
Proof. exact (@lem1300431 x n (@lem1300311 x N n h1 h2)). Qed.
Lemma lem1300454 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1300455 (x : nadd) (N : nat) (n : nat) (h1 : term80 N x) (h2 : Peano.le N n) : (term186 x n) = (or False).
Proof. exact (MK_COMB (@lem1300454) (@lem1300453 x N n h1 h2)). Qed.
Lemma lem1300457 (m : nat) : (term179 m) = False.
Proof. exact (EQ_MP (@lem1300411 m) (@lem1300410 m)). Qed.
Lemma lem1300458 (x : nadd) (n : nat) : (term187 x n) = False.
Proof. exact (@lem1300457 (dest_nadd x n)). Qed.
Lemma lem1300459 (x : nadd) (N : nat) (n : nat) (h1 : term80 N x) (h2 : Peano.le N n) : (term185 x n) = (False \/ False).
Proof. exact (MK_COMB (@lem1300455 x N n h1 h2) (@lem1300458 x n)). Qed.
Lemma lem1300461 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1300462 : (False \/ False) = False.
Proof. exact (@lem1300461 False). Qed.
Lemma lem1300463 (x : nadd) (N : nat) (n : nat) (h1 : term80 N x) (h2 : Peano.le N n) : (term185 x n) = False.
Proof. exact (TRANS (@lem1300459 x N n h1 h2) (@lem1300462)). Qed.
Lemma lem1300464 (x : nadd) (N : nat) (n : nat) (h1 : term80 N x) (h2 : Peano.le N n) : (term184 x n) = False.
Proof. exact (TRANS (@lem1300449 x n) (@lem1300463 x N n h1 h2)). Qed.
Lemma lem1300465 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1300466 (x : nadd) (N : nat) (n : nat) (h1 : term80 N x) (h2 : Peano.le N n) : (term183 x n) = (~ False).
Proof. exact (MK_COMB (@lem1300465) (@lem1300464 x N n h1 h2)). Qed.
Lemma lem1300468 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1300469 (x : nadd) (N : nat) (n : nat) (h1 : term80 N x) (h2 : Peano.le N n) : (term183 x n) = True.
Proof. exact (TRANS (@lem1300466 x N n h1 h2) (@lem1300468)). Qed.
Lemma lem1300470 (x : nadd) (N : nat) (n : nat) (h1 : term80 N x) (h2 : Peano.le N n) : (term170 x n) = True.
Proof. exact (TRANS (@lem1300446 x n) (@lem1300469 x N n h1 h2)). Qed.
Lemma lem1300471 (x : nadd) (N : nat) (n : nat) (h1 : term80 N x) (h2 : Peano.le N n) : True = (term170 x n).
Proof. exact (SYM (@lem1300470 x N n h1 h2)). Qed.
Lemma lem1300472 (x : nadd) (N : nat) (n : nat) (h1 : term80 N x) (h2 : Peano.le N n) : term170 x n.
Proof. exact (EQ_MP (@lem1300471 x N n h1 h2) (@lem0)). Qed.
Lemma lem1300473 (x : nadd) (N : nat) (n : nat) (h1 : term80 N x) (h2 : Peano.le N n) : term169 x n.
Proof. exact (EQ_MP (@lem1300401 x n) (@lem1300472 x N n h1 h2)). Qed.
Lemma lem1300474 (A2 : nat) (x : nadd) (N : nat) (n : nat) (h1 : term80 N x) (h2 : Peano.le N n) : term166 A2 x n.
Proof. exact (or_intro2 (A2 = (NUMERAL 0)) (@lem1300473 x N n h1 h2)). Qed.
Lemma lem1300475 (A2 : nat) (x : nadd) (N : nat) (n : nat) (h1 : term80 N x) (h2 : Peano.le N n) : term165 A2 x n.
Proof. exact (EQ_MP (@lem1300394 A2 x n) (@lem1300474 A2 x N n h1 h2)). Qed.
Lemma lem1300476 (A2 : nat) (x : nadd) (N : nat) (n : nat) (h1 : term80 N x) (h2 : Peano.le N n) : term161 A2 x n.
Proof. exact (EQ_MP (@lem1300386 A2 x n) (@lem1300475 A2 x N n h1 h2)). Qed.
Lemma lem1300477 (A1 : nat) (A2 : nat) (x : nadd) (N : nat) (n : nat) (h1 : term125 A1 x A2) (h2 : term80 N x) (h3 : Peano.le N n) : term162 A1 A2 x n.
Proof. exact (EQ_MP (@lem1300378 n A1 x A2 h1) (@lem1300476 A2 x N n h2 h3)). Qed.
Lemma lem1300478 (A1 : nat) (A2 : nat) (x : nadd) (N : nat) (n : nat) (h1 : term125 A1 x A2) (h2 : term80 N x) (h3 : Peano.le N n) : term188 A1 A2 x n.
Proof. exact (ex_intro (term189 A1 A2 x n) (term119 A1 x n A2) (@lem1300477 A1 A2 x N n h1 h2 h3)). Qed.
Lemma lem1300479 (A1 : nat) (A2 : nat) (x : nadd) (N : nat) (n : nat) (h1 : term125 A1 x A2) (h2 : term80 N x) (h3 : Peano.le N n) : term190 A1 A2 x n.
Proof. exact (@lem1300314 A1 A2 x n (@lem1300478 A1 A2 x N n h1 h2 h3)). Qed.
Lemma lem1300480 (n : nat) (A1 : nat) (A2 : nat) (N : nat) (x : nadd) (h1 : term125 A1 x A2) (h2 : term80 N x) : term191 N A1 A2 x n.
Proof. exact (fun h0 : Peano.le N n => @lem1300479 A1 A2 x N n h1 h2 h0). Qed.
Lemma lem1300485 (A1 : nat) (A2 : nat) (N : nat) (x : nadd) (h1 : term125 A1 x A2) (h2 : term80 N x) : term192 N A1 A2 x.
Proof. exact (fun n : nat => @lem1300480 n A1 A2 N x h1 h2). Qed.
Lemma lem1300486 (A1 : nat) (A2 : nat) (N : nat) (x : nadd) (h1 : term125 A1 x A2) (h2 : term80 N x) : term193 A1 A2 x.
Proof. exact (ex_intro (term194 A1 A2 x) N (@lem1300485 A1 A2 N x h1 h2)). Qed.
Lemma lem1300487 (A1 : nat) (A2 : nat) (N : nat) (x : nadd) (h1 : term125 A1 x A2) (h2 : term80 N x) : term134 x.
Proof. exact (ex_intro (term195 x) (Nat.add A1 A2) (@lem1300486 A1 A2 N x h1 h2)). Qed.
Lemma lem1300488 (N : nat) (A1 : nat) (x : nadd) (h1 : term80 N x) (h2 : term128 A1 x) : term134 x.
Proof. exact (ex_elim (@lem1300303 A1 x h2) (fun A2 : nat => fun h0 : term127 A1 x A2 => @lem1300487 A1 A2 N x h0 h1)). Qed.
Lemma lem1300489 (N : nat) (x : nadd) (h1 : term80 N x) (h2 : term131 x) : term134 x.
Proof. exact (ex_elim (@lem1300302 x h2) (fun A1 : nat => fun h0 : term130 x A1 => @lem1300488 N A1 x h1 h0)). Qed.
Lemma lem1300490 (N : nat) (x : nadd) (h1 : term80 N x) : term136 x.
Proof. exact (fun h0 : term131 x => @lem1300489 N x h1 h0). Qed.
Lemma lem1300491 (N : nat) (x : nadd) (h1 : term80 N x) : term135 x.
Proof. exact (EQ_MP (@lem1300301 x) (@lem1300490 N x h1)). Qed.
Lemma lem1300492 (N : nat) (x : nadd) (h1 : term72 x) (h2 : term80 N x) : term134 x.
Proof. exact (@lem1300491 N x h2 (@lem1300171 x h1)). Qed.
Lemma lem1300493 (N : nat) (x : nadd) (h1 : term80 N x) : term196 x.
Proof. exact (fun h0 : term72 x => @lem1300492 N x h0 h1). Qed.
Lemma lem1300494 (N : nat) (x : nadd) (h1 : term80 N x) (h2 : term70 x) : term134 x.
Proof. exact (@lem1300493 N x h1 (@lem1300167 x h2)). Qed.
Lemma lem1300495 (x : nadd) (h1 : term70 x) : term134 x.
Proof. exact (ex_elim (@lem1300161 x h1) (fun N : nat => fun h0 : term197 x N => @lem1300494 N x h0 h1)). Qed.
Lemma lem1300496 (x : nadd) : term198 x.
Proof. exact (fun h0 : term70 x => @lem1300495 x h0). Qed.
Lemma lem1300501 : term199.
Proof. exact (fun x : nadd => @lem1300496 x). Qed.
