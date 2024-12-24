Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INF_FINITE_LEMMA_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import IN_INSERT_spec.
Require Import MEMBER_NOT_EMPTY_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_INSERT_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339577_spec.
Require Import thm1339697_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem5214028 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5214029 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5214030 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5214029 t1) (@lem5214028 t1)). Qed.
Lemma lem5214031 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5214030 t1 t2). Qed.
Lemma lem5214032 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5214033 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5214032 t1 t2) (@lem5214031 t1 t2)). Qed.
Lemma lem5214034 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5214033 t1 t2 t3). Qed.
Lemma lem5214035 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5214036 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5214035 t1 t2 t3) (@lem5214034 t1 t2 t3)). Qed.
Lemma lem5214037 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5214036 t1 t2 t3)). Qed.
Lemma lem5214039 {A : Type'} (s : A -> Prop) (h1 : (term7 A s) = (term8 A s)) : (term7 A s) = (term8 A s).
Proof. exact (h1). Qed.
Lemma lem5214040 {A : Type'} (s : A -> Prop) (h1 : (term7 A s) = (term8 A s)) : (term8 A s) = (term7 A s).
Proof. exact (SYM (@lem5214039 A s h1)). Qed.
Lemma lem5214041 {A : Type'} (s : A -> Prop) (h1 : (term8 A s) = (term7 A s)) : (term8 A s) = (term7 A s).
Proof. exact (h1). Qed.
Lemma lem5214042 {A : Type'} (s : A -> Prop) (h1 : (term8 A s) = (term7 A s)) : (term7 A s) = (term8 A s).
Proof. exact (SYM (@lem5214041 A s h1)). Qed.
Lemma lem5214043 {A : Type'} (s : A -> Prop) : ((term7 A s) = (term8 A s)) = ((term8 A s) = (term7 A s)).
Proof. exact (prop_ext (fun h1 : (term7 A s) = (term8 A s) => @lem5214040 A s h1) (fun h1 : (term8 A s) = (term7 A s) => @lem5214042 A s h1)). Qed.
Lemma lem5214044 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5214043 A s)). Qed.
Lemma lem5214045 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5214046 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (MK_COMB (@lem5214045 A) (@lem5214044 A)). Qed.
Lemma lem5214047 {A : Type'} : term12 A.
Proof. exact (EQ_MP (@lem5214046 A) (@lem3216368 A)). Qed.
Lemma lem5214048 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (@lem5214047 A s). Qed.
Lemma lem5214049 {A : Type'} (s : A -> Prop) : (term13 A s) = ((term8 A s) = (term7 A s)).
Proof. exact (eq_refl (term13 A s)). Qed.
Lemma lem5214051 {A : Type'} (x : A) : term14 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem5214052 {A : Type'} (x : A) : (term14 A x) = (term15 A x).
Proof. exact (eq_refl (term14 A x)). Qed.
Lemma lem5214053 {A : Type'} (x : A) : term15 A x.
Proof. exact (EQ_MP (@lem5214052 A x) (@lem5214051 A x)). Qed.
Lemma lem5214054 {A : Type'} (x : A) (y : A) : term16 A x y.
Proof. exact (@lem5214053 A x y). Qed.
Lemma lem5214055 {A : Type'} (y : A) (x : A) : (term16 A x y) = (term17 A y x).
Proof. exact (eq_refl (term16 A x y)). Qed.
Lemma lem5214056 {A : Type'} (y : A) (x : A) : term17 A y x.
Proof. exact (EQ_MP (@lem5214055 A y x) (@lem5214054 A x y)). Qed.
Lemma lem5214057 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term18 A y x s.
Proof. exact (@lem5214056 A y x s). Qed.
Lemma lem5214058 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term18 A y x s) = ((term19 A x y s) = (term20 A y x s)).
Proof. exact (eq_refl (term18 A y x s)). Qed.
Lemma lem5214060 {A : Type'} (x : A) : term21 A x.
Proof. exact (@lem3278799 A x). Qed.
Lemma lem5214061 {A : Type'} (x : A) : (term21 A x) = (term22 A x).
Proof. exact (eq_refl (term21 A x)). Qed.
Lemma lem5214062 {A : Type'} (x : A) : term22 A x.
Proof. exact (EQ_MP (@lem5214061 A x) (@lem5214060 A x)). Qed.
Lemma lem5214063 {A : Type'} (x : A) (s : A -> Prop) : term23 A x s.
Proof. exact (@lem5214062 A x s). Qed.
Lemma lem5214064 {A : Type'} (x : A) (s : A -> Prop) : (term23 A x s) = (term24 A x s).
Proof. exact (eq_refl (term23 A x s)). Qed.
Lemma lem5214065 {A : Type'} (x : A) (s : A -> Prop) : term24 A x s.
Proof. exact (EQ_MP (@lem5214064 A x s) (@lem5214063 A x s)). Qed.
Lemma lem5214066 {A : Type'} (x : A) (s : A -> Prop) : term25 A x s.
Proof. exact (@lem82 ((@INSERT A x s) = (@EMPTY A))). Qed.
Lemma lem5214079 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (h1). Qed.
Lemma lem5214080 {A : Type'} (P : type686 A) (h1 : term26 A) : term27 A P.
Proof. exact (@lem5214079 A h1 P). Qed.
Lemma lem5214081 {A : Type'} (P : type686 A) : (term27 A P) = (term28 A P).
Proof. exact (eq_refl (term27 A P)). Qed.
Lemma lem5214082 {A : Type'} (P : type686 A) (h1 : term26 A) : term28 A P.
Proof. exact (EQ_MP (@lem5214081 A P) (@lem5214080 A P h1)). Qed.
Lemma lem5214083 {A : Type'} (P : type686 A) (h1 : term29 A P) : term29 A P.
Proof. exact (h1). Qed.
Lemma lem5214084 {A : Type'} (P : type686 A) (h1 : term26 A) (h2 : term29 A P) : term30 A P.
Proof. exact (@lem5214082 A P h1 (@lem5214083 A P h2)). Qed.
Lemma lem5214085 {A : Type'} (P : type686 A) (h1 : term29 A P) : term31 A P.
Proof. exact (fun h0 : term26 A => @lem5214084 A P h0 h1). Qed.
Lemma lem5214086 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (h1). Qed.
Lemma lem5214087 {A : Type'} (P : type686 A) (h1 : term26 A) (h2 : term29 A P) : term30 A P.
Proof. exact (@lem5214085 A P h2 (@lem5214086 A h1)). Qed.
Lemma lem5214088 {A : Type'} (P : type686 A) (h1 : term26 A) : term28 A P.
Proof. exact (fun h0 : term29 A P => @lem5214087 A P h1 h0). Qed.
Lemma lem5214089 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (fun P : type686 A => @lem5214088 A P h1). Qed.
Lemma lem5214090 {A : Type'} : term32 A.
Proof. exact (fun h0 : term26 A => @lem5214089 A h0). Qed.
Lemma lem5214091 {A : Type'} : term26 A.
Proof. exact (@lem5214090 A (@lem3558722 A)). Qed.
Lemma lem5214092 {A : Type'} (P : type686 A) : term27 A P.
Proof. exact (@lem5214091 A P). Qed.
Lemma lem5214093 {A : Type'} (P : type686 A) : (term27 A P) = (term28 A P).
Proof. exact (eq_refl (term27 A P)). Qed.
Lemma lem5214100 (p : Prop) (q : Prop) (r : Prop) : (term33 p q r) = (term34 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem5214101 (s : real -> Prop) : (term35 s) = (term36 s).
Proof. exact (@lem5214100 (@FINITE real s) (term37 s) (term38 s)). Qed.
Lemma lem5214120 : term39 = term40.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5214101 s)). Qed.
Lemma lem5214121 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5214122 : term41 = term42.
Proof. exact (MK_COMB (@lem5214121) (@lem5214120)). Qed.
Lemma lem5214127 : term42 = term41.
Proof. exact (SYM (@lem5214122)). Qed.
Lemma lem5214129 {A : Type'} (P : type686 A) : term28 A P.
Proof. exact (EQ_MP (@lem5214093 A P) (@lem5214092 A P)). Qed.
Lemma lem5214130 (P : type1022) : term43 P.
Proof. exact (@lem5214129 real P). Qed.
Lemma lem5214131 : term44.
Proof. exact (@lem5214130 term45). Qed.
Lemma lem5214132 : term46 = term47.
Proof. exact (eq_refl term46). Qed.
Lemma lem5214133 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5214134 : term48 = term49.
Proof. exact (MK_COMB (@lem5214133) (@lem5214132)). Qed.
Lemma lem5214135 (s : real -> Prop) : (term50 s) = (term51 s).
Proof. exact (eq_refl (term50 s)). Qed.
Lemma lem5214136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5214137 (s : real -> Prop) : (term52 s) = (term53 s).
Proof. exact (MK_COMB (@lem5214136) (@lem5214135 s)). Qed.
Lemma lem5214138 (x : real) (s : real -> Prop) : (term54 x s) = (term54 x s).
Proof. exact (eq_refl (term54 x s)). Qed.
Lemma lem5214139 (x : real) (s : real -> Prop) : (term55 x s) = (term56 x s).
Proof. exact (MK_COMB (@lem5214137 s) (@lem5214138 x s)). Qed.
Lemma lem5214140 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5214141 (x : real) (s : real -> Prop) : (term57 x s) = (term58 x s).
Proof. exact (MK_COMB (@lem5214140) (@lem5214139 x s)). Qed.
Lemma lem5214142 (x : real) (s : real -> Prop) : (term59 x s) = (term60 x s).
Proof. exact (eq_refl (term59 x s)). Qed.
Lemma lem5214143 (x : real) (s : real -> Prop) : (term61 x s) = (term62 x s).
Proof. exact (MK_COMB (@lem5214141 x s) (@lem5214142 x s)). Qed.
Lemma lem5214144 (x : real) : (term63 x) = (term64 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5214143 x s)). Qed.
Lemma lem5214145 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5214146 (x : real) : (term65 x) = (term66 x).
Proof. exact (MK_COMB (@lem5214145) (@lem5214144 x)). Qed.
Lemma lem5214147 : term67 = term68.
Proof. exact (fun_ext (fun x : real => @lem5214146 x)). Qed.
Lemma lem5214148 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5214149 : term69 = term70.
Proof. exact (MK_COMB (@lem5214148) (@lem5214147)). Qed.
Lemma lem5214150 : term71 = term72.
Proof. exact (MK_COMB (@lem5214134) (@lem5214149)). Qed.
Lemma lem5214151 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5214152 : term73 = term74.
Proof. exact (MK_COMB (@lem5214151) (@lem5214150)). Qed.
Lemma lem5214153 (s : real -> Prop) : (term50 s) = (term51 s).
Proof. exact (eq_refl (term50 s)). Qed.
Lemma lem5214154 (s : real -> Prop) : (term75 s) = (term75 s).
Proof. exact (eq_refl (term75 s)). Qed.
Lemma lem5214155 (s : real -> Prop) : (term76 s) = (term36 s).
Proof. exact (MK_COMB (@lem5214154 s) (@lem5214153 s)). Qed.
Lemma lem5214156 : term77 = term40.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5214155 s)). Qed.
Lemma lem5214157 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5214158 : term78 = term42.
Proof. exact (MK_COMB (@lem5214157) (@lem5214156)). Qed.
Lemma lem5214159 : term44 = term79.
Proof. exact (MK_COMB (@lem5214152) (@lem5214158)). Qed.
Lemma lem5214160 : term79.
Proof. exact (EQ_MP (@lem5214159) (@lem5214131)). Qed.
Lemma lem5214166 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5214167 (x : real -> Prop) : (x = x) = True.
Proof. exact (@lem5214166 (real -> Prop) x). Qed.
Lemma lem5214168 : ((@EMPTY real) = (@EMPTY real)) = True.
Proof. exact (@lem5214167 (@EMPTY real)). Qed.
Lemma lem5214169 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5214170 : term80 = (~ True).
Proof. exact (MK_COMB (@lem5214169) (@lem5214168)). Qed.
Lemma lem5214172 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem5214173 : term80 = False.
Proof. exact (TRANS (@lem5214170) (@lem5214172)). Qed.
Lemma lem5214174 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5214175 : term81 = (imp False).
Proof. exact (MK_COMB (@lem5214174) (@lem5214173)). Qed.
Lemma lem5214188 : term82 = term82.
Proof. exact (eq_refl term82). Qed.
Lemma lem5214189 : term47 = term83.
Proof. exact (MK_COMB (@lem5214175) (@lem5214188)). Qed.
Lemma lem5214191 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5214192 : term83 = True.
Proof. exact (@lem5214191 term82). Qed.
Lemma lem5214193 : term47 = True.
Proof. exact (TRANS (@lem5214189) (@lem5214192)). Qed.
Lemma lem5214194 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5214195 : term49 = (and True).
Proof. exact (MK_COMB (@lem5214194) (@lem5214193)). Qed.
Lemma lem5214229 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem5214066 A x s (@lem5214065 A x s)). Qed.
Lemma lem5214230 (x : real) (s : real -> Prop) : ((@INSERT real x s) = (@EMPTY real)) = False.
Proof. exact (@lem5214229 real x s). Qed.
Lemma lem5214231 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5214232 (x : real) (s : real -> Prop) : (term84 x s) = (~ False).
Proof. exact (MK_COMB (@lem5214231) (@lem5214230 x s)). Qed.
Lemma lem5214234 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5214235 (x : real) (s : real -> Prop) : (term84 x s) = True.
Proof. exact (TRANS (@lem5214232 x s) (@lem5214234)). Qed.
Lemma lem5214236 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5214237 (x : real) (s : real -> Prop) : (term85 x s) = (imp True).
Proof. exact (MK_COMB (@lem5214236) (@lem5214235 x s)). Qed.
Lemma lem5214245 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term19 A x y s) = (term20 A y x s).
Proof. exact (EQ_MP (@lem5214058 A y x s) (@lem5214057 A y x s)). Qed.
Lemma lem5214246 (y : real) (x : real) (s : real -> Prop) : (term86 x y s) = (term87 y x s).
Proof. exact (@lem5214245 real y x s). Qed.
Lemma lem5214247 (x : real) (b : real) (s : real -> Prop) : (term86 b x s) = (term87 x b s).
Proof. exact (@lem5214246 x b s). Qed.
Lemma lem5214252 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5214253 (x : real) (b : real) (s : real -> Prop) : (term88 b x s) = (term89 x b s).
Proof. exact (MK_COMB (@lem5214252) (@lem5214247 x b s)). Qed.
Lemma lem5214261 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term19 A x y s) = (term20 A y x s).
Proof. exact (EQ_MP (@lem5214058 A y x s) (@lem5214057 A y x s)). Qed.
Lemma lem5214262 (y : real) (x : real) (s : real -> Prop) : (term86 x y s) = (term87 y x s).
Proof. exact (@lem5214261 real y x s). Qed.
Lemma lem5214263 (x : real) (x' : real) (s : real -> Prop) : (term86 x' x s) = (term87 x x' s).
Proof. exact (@lem5214262 x x' s). Qed.
Lemma lem5214268 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5214269 (x : real) (x' : real) (s : real -> Prop) : (term90 x' x s) = (term91 x x' s).
Proof. exact (MK_COMB (@lem5214268) (@lem5214263 x x' s)). Qed.
Lemma lem5214270 (b : real) (x' : real) : (real_le b x') = (real_le b x').
Proof. exact (eq_refl (real_le b x')). Qed.
Lemma lem5214271 (x : real) (s : real -> Prop) (b : real) (x' : real) : (term92 x s b x') = (term93 x s b x').
Proof. exact (MK_COMB (@lem5214269 x x' s) (@lem5214270 b x')). Qed.
Lemma lem5214274 (x : real) (s : real -> Prop) (b : real) : (term94 x s b) = (term95 x s b).
Proof. exact (fun_ext (fun x' : real => @lem5214271 x s b x')). Qed.
Lemma lem5214275 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5214276 (x : real) (s : real -> Prop) (b : real) : (term96 x s b) = (term97 x s b).
Proof. exact (MK_COMB (@lem5214275) (@lem5214274 x s b)). Qed.
Lemma lem5214281 (x : real) (s : real -> Prop) (b : real) : (term98 x s b) = (term99 x s b).
Proof. exact (MK_COMB (@lem5214253 x b s) (@lem5214276 x s b)). Qed.
Lemma lem5214284 (x : real) (s : real -> Prop) : (term100 x s) = (term101 x s).
Proof. exact (fun_ext (fun b : real => @lem5214281 x s b)). Qed.
Lemma lem5214285 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5214286 (x : real) (s : real -> Prop) : (term102 x s) = (term103 x s).
Proof. exact (MK_COMB (@lem5214285) (@lem5214284 x s)). Qed.
Lemma lem5214291 (x : real) (s : real -> Prop) : (term60 x s) = (term104 x s).
Proof. exact (MK_COMB (@lem5214237 x s) (@lem5214286 x s)). Qed.
Lemma lem5214293 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5214294 (x : real) (s : real -> Prop) : (term104 x s) = (term103 x s).
Proof. exact (@lem5214293 (term103 x s)). Qed.
Lemma lem5214315 (x : real) (s : real -> Prop) : (term60 x s) = (term103 x s).
Proof. exact (TRANS (@lem5214291 x s) (@lem5214294 x s)). Qed.
Lemma lem5214316 (x : real) (s : real -> Prop) : (term58 x s) = (term58 x s).
Proof. exact (eq_refl (term58 x s)). Qed.
Lemma lem5214317 (x : real) (s : real -> Prop) : (term62 x s) = (term105 x s).
Proof. exact (MK_COMB (@lem5214316 x s) (@lem5214315 x s)). Qed.
Lemma lem5214320 (x : real) : (term64 x) = (term106 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5214317 x s)). Qed.
Lemma lem5214321 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5214322 (x : real) : (term66 x) = (term107 x).
Proof. exact (MK_COMB (@lem5214321) (@lem5214320 x)). Qed.
Lemma lem5214327 : term68 = term108.
Proof. exact (fun_ext (fun x : real => @lem5214322 x)). Qed.
Lemma lem5214328 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5214329 : term70 = term109.
Proof. exact (MK_COMB (@lem5214328) (@lem5214327)). Qed.
Lemma lem5214334 : term72 = term110.
Proof. exact (MK_COMB (@lem5214195) (@lem5214329)). Qed.
Lemma lem5214336 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5214337 : term110 = term109.
Proof. exact (@lem5214336 term109). Qed.
Lemma lem5214388 : term72 = term109.
Proof. exact (TRANS (@lem5214334) (@lem5214337)). Qed.
Lemma lem5214389 : term109 = term72.
Proof. exact (SYM (@lem5214388)). Qed.
Lemma lem5214405 {A : Type'} (s : A -> Prop) : (term8 A s) = (term7 A s).
Proof. exact (EQ_MP (@lem5214049 A s) (@lem5214048 A s)). Qed.
Lemma lem5214406 (s : real -> Prop) : (term37 s) = (term111 s).
Proof. exact (@lem5214405 real s). Qed.
Lemma lem5214411 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5214412 (s : real -> Prop) : (term112 s) = (term113 s).
Proof. exact (MK_COMB (@lem5214411) (@lem5214406 s)). Qed.
Lemma lem5214425 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (eq_refl (term38 s)). Qed.
Lemma lem5214426 (s : real -> Prop) : (term51 s) = (term114 s).
Proof. exact (MK_COMB (@lem5214412 s) (@lem5214425 s)). Qed.
Lemma lem5214429 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5214430 (s : real -> Prop) : (term53 s) = (term115 s).
Proof. exact (MK_COMB (@lem5214429) (@lem5214426 s)). Qed.
Lemma lem5214433 (x : real) (s : real -> Prop) : (term54 x s) = (term54 x s).
Proof. exact (eq_refl (term54 x s)). Qed.
Lemma lem5214434 (x : real) (s : real -> Prop) : (term56 x s) = (term116 x s).
Proof. exact (MK_COMB (@lem5214430 s) (@lem5214433 x s)). Qed.
Lemma lem5214437 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5214438 (x : real) (s : real -> Prop) : (term58 x s) = (term117 x s).
Proof. exact (MK_COMB (@lem5214437) (@lem5214434 x s)). Qed.
Lemma lem5214459 (x : real) (s : real -> Prop) : (term103 x s) = (term103 x s).
Proof. exact (eq_refl (term103 x s)). Qed.
Lemma lem5214460 (x : real) (s : real -> Prop) : (term105 x s) = (term118 x s).
Proof. exact (MK_COMB (@lem5214438 x s) (@lem5214459 x s)). Qed.
Lemma lem5214463 (x : real) : (term106 x) = (term119 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5214460 x s)). Qed.
Lemma lem5214464 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5214465 (x : real) : (term107 x) = (term120 x).
Proof. exact (MK_COMB (@lem5214464) (@lem5214463 x)). Qed.
Lemma lem5214470 : term108 = term121.
Proof. exact (fun_ext (fun x : real => @lem5214465 x)). Qed.
Lemma lem5214471 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5214472 : term109 = term122.
Proof. exact (MK_COMB (@lem5214471) (@lem5214470)). Qed.
Lemma lem5214477 : term122 = term109.
Proof. exact (SYM (@lem5214472)). Qed.
Lemma lem5214479 (p : Prop) : p = (term123 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5214480 : term122 = term124.
Proof. exact (@lem5214479 term122). Qed.
Lemma lem5214481 : term124 = term122.
Proof. exact (SYM (@lem5214480)). Qed.
Lemma lem5214482 (h1 : term125) : term125.
Proof. exact (h1). Qed.
Lemma lem5214485 (h1 : term126) : term126.
Proof. exact (h1). Qed.
Lemma lem5214486 : term127.
Proof. exact (fun h0 : term126 => @lem5214485 h0). Qed.
Lemma lem5214487 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem5214488 (h1 : term126) : term126.
Proof. exact (h1). Qed.
Lemma lem5214489 (h1 : term126) (h2 : term127) : term126.
Proof. exact (@lem5214487 h2 (@lem5214488 h1)). Qed.
Lemma lem5214490 (h1 : term126) : term128.
Proof. exact (fun h0 : term127 => @lem5214489 h1 h0). Qed.
Lemma lem5214491 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem5214492 (h1 : term126) (h2 : term127) : term126.
Proof. exact (@lem5214490 h1 (@lem5214491 h2)). Qed.
Lemma lem5214493 (h1 : term127) : term127.
Proof. exact (fun h0 : term126 => @lem5214492 h0 h1). Qed.
Lemma lem5214494 : term129.
Proof. exact (fun h0 : term127 => @lem5214493 h0). Qed.
Lemma lem5214497 : term127.
Proof. exact (@lem5214494 (@lem5214486)). Qed.
Lemma lem5214655 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5214656 : term130 = term131.
Proof. exact (@lem5214655 term132). Qed.
Lemma lem5214711 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5214712 : term134 = term135.
Proof. exact (MK_COMB (@lem5214711) (@lem5214656)). Qed.
Lemma lem5214715 : term136 = term136.
Proof. exact (eq_refl term136). Qed.
Lemma lem5214722 : term126 = term137.
Proof. exact (MK_COMB (@lem5214715) (@lem5214712)). Qed.
Lemma lem5214727 (y : real) (x : real) : (term138 y x) = (term138 y x).
Proof. exact (eq_refl (term138 y x)). Qed.
Lemma lem5214728 (x : real) : (term139 x) = (term139 x).
Proof. exact (fun_ext (fun y : real => @lem5214727 y x)). Qed.
Lemma lem5214729 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5214730 (x : real) : (term140 x) = (term140 x).
Proof. exact (MK_COMB (@lem5214729) (@lem5214728 x)). Qed.
Lemma lem5214731 : term141 = term141.
Proof. exact (fun_ext (fun x : real => @lem5214730 x)). Qed.
Lemma lem5214732 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5214733 : term132 = term132.
Proof. exact (MK_COMB (@lem5214732) (@lem5214731)). Qed.
Lemma lem5214734 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5214735 : term131 = term131.
Proof. exact (MK_COMB (@lem5214734) (@lem5214733)). Qed.
Lemma lem5214744 (y : real) (x : real) (z : real) : (term142 y x z) = (term142 y x z).
Proof. exact (eq_refl (term142 y x z)). Qed.
Lemma lem5214745 (y : real) (x : real) : (term143 y x) = (term143 y x).
Proof. exact (fun_ext (fun z : real => @lem5214744 y x z)). Qed.
Lemma lem5214746 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5214747 (y : real) (x : real) : (term144 y x) = (term144 y x).
Proof. exact (MK_COMB (@lem5214746) (@lem5214745 y x)). Qed.
Lemma lem5214748 (x : real) : (term145 x) = (term145 x).
Proof. exact (fun_ext (fun y : real => @lem5214747 y x)). Qed.
Lemma lem5214749 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5214750 (x : real) : (term146 x) = (term146 x).
Proof. exact (MK_COMB (@lem5214749) (@lem5214748 x)). Qed.
Lemma lem5214751 : term147 = term147.
Proof. exact (fun_ext (fun x : real => @lem5214750 x)). Qed.
Lemma lem5214752 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5214753 : term148 = term148.
Proof. exact (MK_COMB (@lem5214752) (@lem5214751)). Qed.
Lemma lem5214754 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5214755 : term133 = term133.
Proof. exact (MK_COMB (@lem5214754) (@lem5214753)). Qed.
Lemma lem5214756 : term135 = term135.
Proof. exact (MK_COMB (@lem5214755) (@lem5214735)). Qed.
Lemma lem5214765 (x : real) (s : real -> Prop) (b : real) (x' : real) : (term93 x s b x') = (term93 x s b x').
Proof. exact (eq_refl (term93 x s b x')). Qed.
Lemma lem5214766 (x : real) (s : real -> Prop) (b : real) : (term95 x s b) = (term95 x s b).
Proof. exact (fun_ext (fun x' : real => @lem5214765 x s b x')). Qed.
Lemma lem5214767 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5214768 (x : real) (s : real -> Prop) (b : real) : (term97 x s b) = (term97 x s b).
Proof. exact (MK_COMB (@lem5214767) (@lem5214766 x s b)). Qed.
Lemma lem5214775 (x : real) (b : real) (s : real -> Prop) : (term89 x b s) = (term89 x b s).
Proof. exact (eq_refl (term89 x b s)). Qed.
Lemma lem5214776 (x : real) (s : real -> Prop) (b : real) : (term99 x s b) = (term99 x s b).
Proof. exact (MK_COMB (@lem5214775 x b s) (@lem5214768 x s b)). Qed.
Lemma lem5214777 (x : real) (s : real -> Prop) : (term101 x s) = (term101 x s).
Proof. exact (fun_ext (fun b : real => @lem5214776 x s b)). Qed.
Lemma lem5214778 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5214779 (x : real) (s : real -> Prop) : (term103 x s) = (term103 x s).
Proof. exact (MK_COMB (@lem5214778) (@lem5214777 x s)). Qed.
Lemma lem5214786 (x : real) (s : real -> Prop) : (term54 x s) = (term54 x s).
Proof. exact (eq_refl (term54 x s)). Qed.
Lemma lem5214791 (s : real -> Prop) (b : real) (x : real) : (term149 s b x) = (term149 s b x).
Proof. exact (eq_refl (term149 s b x)). Qed.
Lemma lem5214792 (s : real -> Prop) (b : real) : (term150 s b) = (term150 s b).
Proof. exact (fun_ext (fun x : real => @lem5214791 s b x)). Qed.
Lemma lem5214793 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5214794 (s : real -> Prop) (b : real) : (term151 s b) = (term151 s b).
Proof. exact (MK_COMB (@lem5214793) (@lem5214792 s b)). Qed.
Lemma lem5214797 (b : real) (s : real -> Prop) : (term152 b s) = (term152 b s).
Proof. exact (eq_refl (term152 b s)). Qed.
Lemma lem5214798 (s : real -> Prop) (b : real) : (term153 s b) = (term153 s b).
Proof. exact (MK_COMB (@lem5214797 b s) (@lem5214794 s b)). Qed.
Lemma lem5214799 (s : real -> Prop) : (term154 s) = (term154 s).
Proof. exact (fun_ext (fun b : real => @lem5214798 s b)). Qed.
Lemma lem5214800 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5214801 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (MK_COMB (@lem5214800) (@lem5214799 s)). Qed.
Lemma lem5214802 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5214803 (s : real -> Prop) : (term155 s) = (term155 s).
Proof. exact (fun_ext (fun x : real => @lem5214802 x s)). Qed.
Lemma lem5214804 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5214805 (s : real -> Prop) : (term111 s) = (term111 s).
Proof. exact (MK_COMB (@lem5214804) (@lem5214803 s)). Qed.
Lemma lem5214806 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5214807 (s : real -> Prop) : (term113 s) = (term113 s).
Proof. exact (MK_COMB (@lem5214806) (@lem5214805 s)). Qed.
Lemma lem5214808 (s : real -> Prop) : (term114 s) = (term114 s).
Proof. exact (MK_COMB (@lem5214807 s) (@lem5214801 s)). Qed.
Lemma lem5214809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5214810 (s : real -> Prop) : (term115 s) = (term115 s).
Proof. exact (MK_COMB (@lem5214809) (@lem5214808 s)). Qed.
Lemma lem5214811 (x : real) (s : real -> Prop) : (term116 x s) = (term116 x s).
Proof. exact (MK_COMB (@lem5214810 s) (@lem5214786 x s)). Qed.
Lemma lem5214812 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5214813 (x : real) (s : real -> Prop) : (term117 x s) = (term117 x s).
Proof. exact (MK_COMB (@lem5214812) (@lem5214811 x s)). Qed.
Lemma lem5214814 (x : real) (s : real -> Prop) : (term118 x s) = (term118 x s).
Proof. exact (MK_COMB (@lem5214813 x s) (@lem5214779 x s)). Qed.
Lemma lem5214815 (x : real) : (term119 x) = (term119 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5214814 x s)). Qed.
Lemma lem5214816 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5214817 (x : real) : (term120 x) = (term120 x).
Proof. exact (MK_COMB (@lem5214816) (@lem5214815 x)). Qed.
Lemma lem5214818 : term121 = term121.
Proof. exact (fun_ext (fun x : real => @lem5214817 x)). Qed.
Lemma lem5214819 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5214820 : term122 = term122.
Proof. exact (MK_COMB (@lem5214819) (@lem5214818)). Qed.
Lemma lem5214821 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5214822 : term125 = term125.
Proof. exact (MK_COMB (@lem5214821) (@lem5214820)). Qed.
Lemma lem5214823 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5214824 : term136 = term136.
Proof. exact (MK_COMB (@lem5214823) (@lem5214822)). Qed.
Lemma lem5214825 : term137 = term137.
Proof. exact (MK_COMB (@lem5214824) (@lem5214756)). Qed.
Lemma lem5214930 : term126 = term137.
Proof. exact (TRANS (@lem5214722) (@lem5214825)). Qed.
Lemma lem5214931 : term137 = term126.
Proof. exact (SYM (@lem5214930)). Qed.
Lemma lem5214932 (h1 : term125) : term125.
Proof. exact (h1). Qed.
Lemma lem5214933 (h1 : term148) : term148.
Proof. exact (h1). Qed.
Lemma lem5214934 (h1 : term132) : term132.
Proof. exact (h1). Qed.
Lemma lem5214936 (P : real -> Prop) : (term156 P) = (term157 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5214937 (s : real -> Prop) : (term158 s) = (term159 s).
Proof. exact (@lem5214936 (term155 s)). Qed.
Lemma lem5214938 (x : real) (s : real -> Prop) : (term160 s x) = (@IN real x s).
Proof. exact (eq_refl (term160 s x)). Qed.
Lemma lem5214939 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5214941 (x : real) (s : real -> Prop) : (term161 s x) = (term162 x s).
Proof. exact (MK_COMB (@lem5214939) (@lem5214938 x s)). Qed.
Lemma lem5214942 (s : real -> Prop) : (term163 s) = (term164 s).
Proof. exact (fun_ext (fun x : real => @lem5214941 x s)). Qed.
Lemma lem5214943 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5214944 (s : real -> Prop) : (term159 s) = (term165 s).
Proof. exact (MK_COMB (@lem5214943) (@lem5214942 s)). Qed.
Lemma lem5214945 (s : real -> Prop) : (term158 s) = (term165 s).
Proof. exact (TRANS (@lem5214937 s) (@lem5214944 s)). Qed.
Lemma lem5214953 (s : real -> Prop) (b : real) (x : real) : (term149 s b x) = (term166 s b x).
Proof. exact (@lem17265 (@IN real x s) (real_le b x)). Qed.
Lemma lem5214954 (s : real -> Prop) (b : real) : (term150 s b) = (term167 s b).
Proof. exact (fun_ext (fun x : real => @lem5214953 s b x)). Qed.
Lemma lem5214955 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5214956 (s : real -> Prop) (b : real) : (term151 s b) = (term168 s b).
Proof. exact (MK_COMB (@lem5214955) (@lem5214954 s b)). Qed.
Lemma lem5214958 (b : real) (s : real -> Prop) : (term152 b s) = (term152 b s).
Proof. exact (eq_refl (term152 b s)). Qed.
Lemma lem5214959 (s : real -> Prop) (b : real) : (term153 s b) = (term169 s b).
Proof. exact (MK_COMB (@lem5214958 b s) (@lem5214956 s b)). Qed.
Lemma lem5214960 (s : real -> Prop) : (term154 s) = (term170 s).
Proof. exact (fun_ext (fun b : real => @lem5214959 s b)). Qed.
Lemma lem5214961 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5214962 (s : real -> Prop) : (term38 s) = (term171 s).
Proof. exact (MK_COMB (@lem5214961) (@lem5214960 s)). Qed.
Lemma lem5214963 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5214964 (s : real -> Prop) : (term172 s) = (term173 s).
Proof. exact (MK_COMB (@lem5214963) (@lem5214945 s)). Qed.
Lemma lem5214965 (s : real -> Prop) : (term174 s) = (term175 s).
Proof. exact (MK_COMB (@lem5214964 s) (@lem5214962 s)). Qed.
Lemma lem5214966 (s : real -> Prop) : (term114 s) = (term174 s).
Proof. exact (@lem17265 (term111 s) (term38 s)). Qed.
Lemma lem5214967 (s : real -> Prop) : (term114 s) = (term175 s).
Proof. exact (TRANS (@lem5214966 s) (@lem5214965 s)). Qed.
Lemma lem5214972 (x : real) (s : real -> Prop) : (term54 x s) = (term54 x s).
Proof. exact (eq_refl (term54 x s)). Qed.
Lemma lem5214973 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5214974 (s : real -> Prop) : (term115 s) = (term176 s).
Proof. exact (MK_COMB (@lem5214973) (@lem5214967 s)). Qed.
Lemma lem5214975 (x : real) (s : real -> Prop) : (term116 x s) = (term177 x s).
Proof. exact (MK_COMB (@lem5214974 s) (@lem5214972 x s)). Qed.
Lemma lem5214982 (x : real) (b : real) (s : real -> Prop) : (term178 x b s) = (term179 x b s).
Proof. exact (@lem17160 (b = x) (@IN real b s)). Qed.
Lemma lem5214993 (x : real) (s : real -> Prop) (b : real) (x' : real) : (term180 x s b x') = (term181 x s b x').
Proof. exact (@lem17362 (term87 x x' s) (real_le b x')). Qed.
Lemma lem5214994 (P : real -> Prop) : (term182 P) = (term183 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5214995 (x : real) (s : real -> Prop) (b : real) : (term184 x s b) = (term185 x s b).
Proof. exact (@lem5214994 (term95 x s b)). Qed.
Lemma lem5214996 (x : real) (s : real -> Prop) (b : real) (x' : real) : (term186 x s b x') = (term93 x s b x').
Proof. exact (eq_refl (term186 x s b x')). Qed.
Lemma lem5214997 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5214998 (x : real) (s : real -> Prop) (b : real) (x' : real) : (term187 x s b x') = (term180 x s b x').
Proof. exact (MK_COMB (@lem5214997) (@lem5214996 x s b x')). Qed.
Lemma lem5214999 (x : real) (s : real -> Prop) (b : real) (x' : real) : (term187 x s b x') = (term181 x s b x').
Proof. exact (TRANS (@lem5214998 x s b x') (@lem5214993 x s b x')). Qed.
Lemma lem5215000 (x : real) (s : real -> Prop) (b : real) : (term188 x s b) = (term189 x s b).
Proof. exact (fun_ext (fun x' : real => @lem5214999 x s b x')). Qed.
Lemma lem5215001 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5215002 (x : real) (s : real -> Prop) (b : real) : (term185 x s b) = (term190 x s b).
Proof. exact (MK_COMB (@lem5215001) (@lem5215000 x s b)). Qed.
Lemma lem5215003 (x : real) (s : real -> Prop) (b : real) : (term184 x s b) = (term190 x s b).
Proof. exact (TRANS (@lem5214995 x s b) (@lem5215002 x s b)). Qed.
Lemma lem5215004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5215005 (x : real) (b : real) (s : real -> Prop) : (term191 x b s) = (term192 x b s).
Proof. exact (MK_COMB (@lem5215004) (@lem5214982 x b s)). Qed.
Lemma lem5215006 (x : real) (s : real -> Prop) (b : real) : (term193 x s b) = (term194 x s b).
Proof. exact (MK_COMB (@lem5215005 x b s) (@lem5215003 x s b)). Qed.
Lemma lem5215007 (x : real) (s : real -> Prop) (b : real) : (term195 x s b) = (term193 x s b).
Proof. exact (@lem17045 (term87 x b s) (term97 x s b)). Qed.
Lemma lem5215008 (x : real) (s : real -> Prop) (b : real) : (term195 x s b) = (term194 x s b).
Proof. exact (TRANS (@lem5215007 x s b) (@lem5215006 x s b)). Qed.
Lemma lem5215009 (P : real -> Prop) : (term156 P) = (term157 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5215010 (x : real) (s : real -> Prop) : (term196 x s) = (term197 x s).
Proof. exact (@lem5215009 (term101 x s)). Qed.
Lemma lem5215011 (x : real) (s : real -> Prop) (b : real) : (term198 x s b) = (term99 x s b).
Proof. exact (eq_refl (term198 x s b)). Qed.
Lemma lem5215012 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5215013 (x : real) (s : real -> Prop) (b : real) : (term199 x s b) = (term195 x s b).
Proof. exact (MK_COMB (@lem5215012) (@lem5215011 x s b)). Qed.
Lemma lem5215014 (x : real) (s : real -> Prop) (b : real) : (term199 x s b) = (term194 x s b).
Proof. exact (TRANS (@lem5215013 x s b) (@lem5215008 x s b)). Qed.
Lemma lem5215015 (x : real) (s : real -> Prop) : (term200 x s) = (term201 x s).
Proof. exact (fun_ext (fun b : real => @lem5215014 x s b)). Qed.
Lemma lem5215016 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215017 (x : real) (s : real -> Prop) : (term197 x s) = (term202 x s).
Proof. exact (MK_COMB (@lem5215016) (@lem5215015 x s)). Qed.
Lemma lem5215018 (x : real) (s : real -> Prop) : (term196 x s) = (term202 x s).
Proof. exact (TRANS (@lem5215010 x s) (@lem5215017 x s)). Qed.
Lemma lem5215019 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5215020 (x : real) (s : real -> Prop) : (term203 x s) = (term204 x s).
Proof. exact (MK_COMB (@lem5215019) (@lem5214975 x s)). Qed.
Lemma lem5215021 (x : real) (s : real -> Prop) : (term205 x s) = (term206 x s).
Proof. exact (MK_COMB (@lem5215020 x s) (@lem5215018 x s)). Qed.
Lemma lem5215022 (x : real) (s : real -> Prop) : (term207 x s) = (term205 x s).
Proof. exact (@lem17362 (term116 x s) (term103 x s)). Qed.
Lemma lem5215023 (x : real) (s : real -> Prop) : (term207 x s) = (term206 x s).
Proof. exact (TRANS (@lem5215022 x s) (@lem5215021 x s)). Qed.
Lemma lem5215024 (P : type1022) : (term208 P) = (term209 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5215025 (x : real) : (term210 x) = (term211 x).
Proof. exact (@lem5215024 (term119 x)). Qed.
Lemma lem5215026 (x : real) (s : real -> Prop) : (term212 x s) = (term118 x s).
Proof. exact (eq_refl (term212 x s)). Qed.
Lemma lem5215027 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5215028 (x : real) (s : real -> Prop) : (term213 x s) = (term207 x s).
Proof. exact (MK_COMB (@lem5215027) (@lem5215026 x s)). Qed.
Lemma lem5215029 (x : real) (s : real -> Prop) : (term213 x s) = (term206 x s).
Proof. exact (TRANS (@lem5215028 x s) (@lem5215023 x s)). Qed.
Lemma lem5215030 (x : real) : (term214 x) = (term215 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5215029 x s)). Qed.
Lemma lem5215031 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5215032 (x : real) : (term211 x) = (term216 x).
Proof. exact (MK_COMB (@lem5215031) (@lem5215030 x)). Qed.
Lemma lem5215033 (x : real) : (term210 x) = (term216 x).
Proof. exact (TRANS (@lem5215025 x) (@lem5215032 x)). Qed.
Lemma lem5215034 (P : real -> Prop) : (term182 P) = (term183 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5215035 : term125 = term217.
Proof. exact (@lem5215034 term121). Qed.
Lemma lem5215036 (x : real) : (term218 x) = (term120 x).
Proof. exact (eq_refl (term218 x)). Qed.
Lemma lem5215037 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5215038 (x : real) : (term219 x) = (term210 x).
Proof. exact (MK_COMB (@lem5215037) (@lem5215036 x)). Qed.
Lemma lem5215039 (x : real) : (term219 x) = (term216 x).
Proof. exact (TRANS (@lem5215038 x) (@lem5215033 x)). Qed.
Lemma lem5215040 : term220 = term221.
Proof. exact (fun_ext (fun x : real => @lem5215039 x)). Qed.
Lemma lem5215041 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5215042 : term217 = term222.
Proof. exact (MK_COMB (@lem5215041) (@lem5215040)). Qed.
Lemma lem5215043 : term125 = term222.
Proof. exact (TRANS (@lem5215035) (@lem5215042)). Qed.
Lemma lem5215294 {A : Type'} (P : Prop) (Q : A -> Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5215295 (P : Prop) (Q : real -> Prop) : (term225 P Q) = (term226 P Q).
Proof. exact (@lem5215294 real P Q). Qed.
Lemma lem5215296 (s : real -> Prop) : (term227 s) = (term228 s).
Proof. exact (@lem5215295 (term165 s) (term170 s)). Qed.
Lemma lem5215297 (s : real -> Prop) (b : real) : (term229 s b) = (term169 s b).
Proof. exact (eq_refl (term229 s b)). Qed.
Lemma lem5215298 (s : real -> Prop) : (term230 s) = (term170 s).
Proof. exact (fun_ext (fun b : real => @lem5215297 s b)). Qed.
Lemma lem5215299 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5215300 (s : real -> Prop) : (term231 s) = (term171 s).
Proof. exact (MK_COMB (@lem5215299) (@lem5215298 s)). Qed.
Lemma lem5215301 (s : real -> Prop) : (term173 s) = (term173 s).
Proof. exact (eq_refl (term173 s)). Qed.
Lemma lem5215302 (s : real -> Prop) : (term227 s) = (term175 s).
Proof. exact (MK_COMB (@lem5215301 s) (@lem5215300 s)). Qed.
Lemma lem5215303 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5215304 (s : real -> Prop) : (term232 s) = (term233 s).
Proof. exact (MK_COMB (@lem5215303) (@lem5215302 s)). Qed.
Lemma lem5215305 (s : real -> Prop) (b : real) : (term229 s b) = (term169 s b).
Proof. exact (eq_refl (term229 s b)). Qed.
Lemma lem5215306 (s : real -> Prop) : (term173 s) = (term173 s).
Proof. exact (eq_refl (term173 s)). Qed.
Lemma lem5215307 (s : real -> Prop) (b : real) : (term234 s b) = (term235 s b).
Proof. exact (MK_COMB (@lem5215306 s) (@lem5215305 s b)). Qed.
Lemma lem5215308 (s : real -> Prop) : (term236 s) = (term237 s).
Proof. exact (fun_ext (fun b : real => @lem5215307 s b)). Qed.
Lemma lem5215309 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5215310 (s : real -> Prop) : (term228 s) = (term238 s).
Proof. exact (MK_COMB (@lem5215309) (@lem5215308 s)). Qed.
Lemma lem5215311 (s : real -> Prop) : ((term227 s) = (term228 s)) = ((term175 s) = (term238 s)).
Proof. exact (MK_COMB (@lem5215304 s) (@lem5215310 s)). Qed.
Lemma lem5215312 (s : real -> Prop) : (term175 s) = (term238 s).
Proof. exact (EQ_MP (@lem5215311 s) (@lem5215296 s)). Qed.
Lemma lem5215313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5215314 (s : real -> Prop) : (term176 s) = (term239 s).
Proof. exact (MK_COMB (@lem5215313) (@lem5215312 s)). Qed.
Lemma lem5215315 (x : real) (s : real -> Prop) : (term54 x s) = (term54 x s).
Proof. exact (eq_refl (term54 x s)). Qed.
Lemma lem5215316 (x : real) (s : real -> Prop) : (term177 x s) = (term240 x s).
Proof. exact (MK_COMB (@lem5215314 s) (@lem5215315 x s)). Qed.
Lemma lem5215318 {A : Type'} (P : A -> Prop) (Q : Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5215319 (P : real -> Prop) (Q : Prop) : (term243 P Q) = (term244 P Q).
Proof. exact (@lem5215318 real P Q). Qed.
Lemma lem5215320 (x : real) (s : real -> Prop) : (term245 x s) = (term246 x s).
Proof. exact (@lem5215319 (term237 s) (term54 x s)). Qed.
Lemma lem5215321 (s : real -> Prop) (b : real) : (term247 s b) = (term235 s b).
Proof. exact (eq_refl (term247 s b)). Qed.
Lemma lem5215322 (s : real -> Prop) : (term248 s) = (term237 s).
Proof. exact (fun_ext (fun b : real => @lem5215321 s b)). Qed.
Lemma lem5215323 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5215324 (s : real -> Prop) : (term249 s) = (term238 s).
Proof. exact (MK_COMB (@lem5215323) (@lem5215322 s)). Qed.
Lemma lem5215325 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5215326 (s : real -> Prop) : (term250 s) = (term239 s).
Proof. exact (MK_COMB (@lem5215325) (@lem5215324 s)). Qed.
Lemma lem5215327 (x : real) (s : real -> Prop) : (term54 x s) = (term54 x s).
Proof. exact (eq_refl (term54 x s)). Qed.
Lemma lem5215328 (x : real) (s : real -> Prop) : (term245 x s) = (term240 x s).
Proof. exact (MK_COMB (@lem5215326 s) (@lem5215327 x s)). Qed.
Lemma lem5215329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5215330 (x : real) (s : real -> Prop) : (term251 x s) = (term252 x s).
Proof. exact (MK_COMB (@lem5215329) (@lem5215328 x s)). Qed.
Lemma lem5215331 (s : real -> Prop) (b : real) : (term247 s b) = (term235 s b).
Proof. exact (eq_refl (term247 s b)). Qed.
Lemma lem5215332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5215333 (s : real -> Prop) (b : real) : (term253 s b) = (term254 s b).
Proof. exact (MK_COMB (@lem5215332) (@lem5215331 s b)). Qed.
Lemma lem5215334 (x : real) (s : real -> Prop) : (term54 x s) = (term54 x s).
Proof. exact (eq_refl (term54 x s)). Qed.
Lemma lem5215335 (b : real) (x : real) (s : real -> Prop) : (term255 b x s) = (term256 b x s).
Proof. exact (MK_COMB (@lem5215333 s b) (@lem5215334 x s)). Qed.
Lemma lem5215336 (x : real) (s : real -> Prop) : (term257 x s) = (term258 x s).
Proof. exact (fun_ext (fun b : real => @lem5215335 b x s)). Qed.
Lemma lem5215337 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5215338 (x : real) (s : real -> Prop) : (term246 x s) = (term259 x s).
Proof. exact (MK_COMB (@lem5215337) (@lem5215336 x s)). Qed.
Lemma lem5215339 (x : real) (s : real -> Prop) : ((term245 x s) = (term246 x s)) = ((term240 x s) = (term259 x s)).
Proof. exact (MK_COMB (@lem5215330 x s) (@lem5215338 x s)). Qed.
Lemma lem5215340 (x : real) (s : real -> Prop) : (term240 x s) = (term259 x s).
Proof. exact (EQ_MP (@lem5215339 x s) (@lem5215320 x s)). Qed.
Lemma lem5215341 (x : real) (s : real -> Prop) : (term177 x s) = (term259 x s).
Proof. exact (TRANS (@lem5215316 x s) (@lem5215340 x s)). Qed.
Lemma lem5215342 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5215343 (x : real) (s : real -> Prop) : (term204 x s) = (term260 x s).
Proof. exact (MK_COMB (@lem5215342) (@lem5215341 x s)). Qed.
Lemma lem5215345 {A : Type'} (P : Prop) (Q : A -> Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5215346 (P : Prop) (Q : real -> Prop) : (term225 P Q) = (term226 P Q).
Proof. exact (@lem5215345 real P Q). Qed.
Lemma lem5215347 (x : real) (s : real -> Prop) (b : real) : (term261 x s b) = (term262 x s b).
Proof. exact (@lem5215346 (term179 x b s) (term189 x s b)). Qed.
Lemma lem5215348 (x : real) (s : real -> Prop) (b : real) (x' : real) : (term263 x s b x') = (term181 x s b x').
Proof. exact (eq_refl (term263 x s b x')). Qed.
Lemma lem5215349 (x : real) (s : real -> Prop) (b : real) : (term264 x s b) = (term189 x s b).
Proof. exact (fun_ext (fun x' : real => @lem5215348 x s b x')). Qed.
Lemma lem5215350 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5215351 (x : real) (s : real -> Prop) (b : real) : (term265 x s b) = (term190 x s b).
Proof. exact (MK_COMB (@lem5215350) (@lem5215349 x s b)). Qed.
Lemma lem5215352 (x : real) (b : real) (s : real -> Prop) : (term192 x b s) = (term192 x b s).
Proof. exact (eq_refl (term192 x b s)). Qed.
Lemma lem5215353 (x : real) (s : real -> Prop) (b : real) : (term261 x s b) = (term194 x s b).
Proof. exact (MK_COMB (@lem5215352 x b s) (@lem5215351 x s b)). Qed.
Lemma lem5215354 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5215355 (x : real) (s : real -> Prop) (b : real) : (term266 x s b) = (term267 x s b).
Proof. exact (MK_COMB (@lem5215354) (@lem5215353 x s b)). Qed.
Lemma lem5215356 (x : real) (s : real -> Prop) (b : real) (x' : real) : (term263 x s b x') = (term181 x s b x').
Proof. exact (eq_refl (term263 x s b x')). Qed.
Lemma lem5215357 (x : real) (b : real) (s : real -> Prop) : (term192 x b s) = (term192 x b s).
Proof. exact (eq_refl (term192 x b s)). Qed.
Lemma lem5215358 (x : real) (s : real -> Prop) (b : real) (x' : real) : (term268 x s b x') = (term269 x s b x').
Proof. exact (MK_COMB (@lem5215357 x b s) (@lem5215356 x s b x')). Qed.
Lemma lem5215359 (x : real) (s : real -> Prop) (b : real) : (term270 x s b) = (term271 x s b).
Proof. exact (fun_ext (fun x' : real => @lem5215358 x s b x')). Qed.
Lemma lem5215360 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5215361 (x : real) (s : real -> Prop) (b : real) : (term262 x s b) = (term272 x s b).
Proof. exact (MK_COMB (@lem5215360) (@lem5215359 x s b)). Qed.
Lemma lem5215362 (x : real) (s : real -> Prop) (b : real) : ((term261 x s b) = (term262 x s b)) = ((term194 x s b) = (term272 x s b)).
Proof. exact (MK_COMB (@lem5215355 x s b) (@lem5215361 x s b)). Qed.
Lemma lem5215363 (x : real) (s : real -> Prop) (b : real) : (term194 x s b) = (term272 x s b).
Proof. exact (EQ_MP (@lem5215362 x s b) (@lem5215347 x s b)). Qed.
Lemma lem5215364 (x : real) (s : real -> Prop) : (term201 x s) = (term273 x s).
Proof. exact (fun_ext (fun b : real => @lem5215363 x s b)). Qed.
Lemma lem5215365 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215366 (x : real) (s : real -> Prop) : (term202 x s) = (term274 x s).
Proof. exact (MK_COMB (@lem5215365) (@lem5215364 x s)). Qed.
Lemma lem5215368 {A B : Type'} (P : type1413 A B) : (term275 A B P) = (term276 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5215369 (P : type1626) : (term277 P) = (term278 P).
Proof. exact (@lem5215368 real real P). Qed.
Lemma lem5215370 (x : real) (s : real -> Prop) : (term279 x s) = (term280 x s).
Proof. exact (@lem5215369 (term281 x s)). Qed.
Lemma lem5215371 (x : real) (s : real -> Prop) (b : real) : (term282 x s b) = (term271 x s b).
Proof. exact (eq_refl (term282 x s b)). Qed.
Lemma lem5215372 (x' : real) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem5215373 (x : real) (s : real -> Prop) (b : real) (x' : real) : (term283 x s b x') = (term284 x s b x').
Proof. exact (MK_COMB (@lem5215371 x s b) (@lem5215372 x')). Qed.
Lemma lem5215374 (x : real) (s : real -> Prop) (b : real) (x' : real) : (term284 x s b x') = (term269 x s b x').
Proof. exact (eq_refl (term284 x s b x')). Qed.
Lemma lem5215375 (x : real) (s : real -> Prop) (b : real) (x' : real) : (term283 x s b x') = (term269 x s b x').
Proof. exact (TRANS (@lem5215373 x s b x') (@lem5215374 x s b x')). Qed.
Lemma lem5215376 (x : real) (s : real -> Prop) (b : real) : (term285 x s b) = (term271 x s b).
Proof. exact (fun_ext (fun x' : real => @lem5215375 x s b x')). Qed.
Lemma lem5215377 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5215378 (x : real) (s : real -> Prop) (b : real) : (term286 x s b) = (term272 x s b).
Proof. exact (MK_COMB (@lem5215377) (@lem5215376 x s b)). Qed.
Lemma lem5215379 (x : real) (s : real -> Prop) : (term287 x s) = (term273 x s).
Proof. exact (fun_ext (fun b : real => @lem5215378 x s b)). Qed.
Lemma lem5215380 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215381 (x : real) (s : real -> Prop) : (term279 x s) = (term274 x s).
Proof. exact (MK_COMB (@lem5215380) (@lem5215379 x s)). Qed.
Lemma lem5215382 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5215383 (x : real) (s : real -> Prop) : (term288 x s) = (term289 x s).
Proof. exact (MK_COMB (@lem5215382) (@lem5215381 x s)). Qed.
Lemma lem5215384 (x : real) (s : real -> Prop) (b : real) : (term282 x s b) = (term271 x s b).
Proof. exact (eq_refl (term282 x s b)). Qed.
Lemma lem5215385 (x' : real -> real) (b : real) : (x' b) = (x' b).
Proof. exact (eq_refl (x' b)). Qed.
Lemma lem5215386 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term290 x s x' b) = (term291 x s x' b).
Proof. exact (MK_COMB (@lem5215384 x s b) (@lem5215385 x' b)). Qed.
Lemma lem5215387 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term291 x s x' b) = (term292 x s x' b).
Proof. exact (eq_refl (term291 x s x' b)). Qed.
Lemma lem5215388 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term290 x s x' b) = (term292 x s x' b).
Proof. exact (TRANS (@lem5215386 x s x' b) (@lem5215387 x s x' b)). Qed.
Lemma lem5215389 (x : real) (s : real -> Prop) (x' : real -> real) : (term293 x s x') = (term294 x s x').
Proof. exact (fun_ext (fun b : real => @lem5215388 x s x' b)). Qed.
Lemma lem5215390 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215391 (x : real) (s : real -> Prop) (x' : real -> real) : (term295 x s x') = (term296 x s x').
Proof. exact (MK_COMB (@lem5215390) (@lem5215389 x s x')). Qed.
Lemma lem5215392 (x : real) (s : real -> Prop) : (term297 x s) = (term298 x s).
Proof. exact (fun_ext (fun x' : real -> real => @lem5215391 x s x')). Qed.
Lemma lem5215393 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5215394 (x : real) (s : real -> Prop) : (term280 x s) = (term299 x s).
Proof. exact (MK_COMB (@lem5215393) (@lem5215392 x s)). Qed.
Lemma lem5215395 (x : real) (s : real -> Prop) : ((term279 x s) = (term280 x s)) = ((term274 x s) = (term299 x s)).
Proof. exact (MK_COMB (@lem5215383 x s) (@lem5215394 x s)). Qed.
Lemma lem5215396 (x : real) (s : real -> Prop) : (term274 x s) = (term299 x s).
Proof. exact (EQ_MP (@lem5215395 x s) (@lem5215370 x s)). Qed.
Lemma lem5215397 (x : real) (s : real -> Prop) : (term202 x s) = (term299 x s).
Proof. exact (TRANS (@lem5215366 x s) (@lem5215396 x s)). Qed.
Lemma lem5215398 (x : real) (s : real -> Prop) : (term206 x s) = (term300 x s).
Proof. exact (MK_COMB (@lem5215343 x s) (@lem5215397 x s)). Qed.
Lemma lem5215400 {A : Type'} (P : A -> Prop) (Q : Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5215401 (P : real -> Prop) (Q : Prop) : (term243 P Q) = (term244 P Q).
Proof. exact (@lem5215400 real P Q). Qed.
Lemma lem5215402 (x : real) (s : real -> Prop) : (term301 x s) = (term302 x s).
Proof. exact (@lem5215401 (term258 x s) (term299 x s)). Qed.
Lemma lem5215403 (b : real) (x : real) (s : real -> Prop) : (term303 x s b) = (term256 b x s).
Proof. exact (eq_refl (term303 x s b)). Qed.
Lemma lem5215404 (x : real) (s : real -> Prop) : (term304 x s) = (term258 x s).
Proof. exact (fun_ext (fun b : real => @lem5215403 b x s)). Qed.
Lemma lem5215405 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5215406 (x : real) (s : real -> Prop) : (term305 x s) = (term259 x s).
Proof. exact (MK_COMB (@lem5215405) (@lem5215404 x s)). Qed.
Lemma lem5215407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5215408 (x : real) (s : real -> Prop) : (term306 x s) = (term260 x s).
Proof. exact (MK_COMB (@lem5215407) (@lem5215406 x s)). Qed.
Lemma lem5215409 (x : real) (s : real -> Prop) : (term299 x s) = (term299 x s).
Proof. exact (eq_refl (term299 x s)). Qed.
Lemma lem5215410 (x : real) (s : real -> Prop) : (term301 x s) = (term300 x s).
Proof. exact (MK_COMB (@lem5215408 x s) (@lem5215409 x s)). Qed.
Lemma lem5215411 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5215412 (x : real) (s : real -> Prop) : (term307 x s) = (term308 x s).
Proof. exact (MK_COMB (@lem5215411) (@lem5215410 x s)). Qed.
Lemma lem5215413 (b : real) (x : real) (s : real -> Prop) : (term303 x s b) = (term256 b x s).
Proof. exact (eq_refl (term303 x s b)). Qed.
Lemma lem5215414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5215415 (b : real) (x : real) (s : real -> Prop) : (term309 x s b) = (term310 b x s).
Proof. exact (MK_COMB (@lem5215414) (@lem5215413 b x s)). Qed.
Lemma lem5215416 (x : real) (s : real -> Prop) : (term299 x s) = (term299 x s).
Proof. exact (eq_refl (term299 x s)). Qed.
Lemma lem5215417 (b : real) (x : real) (s : real -> Prop) : (term311 b x s) = (term312 b x s).
Proof. exact (MK_COMB (@lem5215415 b x s) (@lem5215416 x s)). Qed.
Lemma lem5215418 (x : real) (s : real -> Prop) : (term313 x s) = (term314 x s).
Proof. exact (fun_ext (fun b : real => @lem5215417 b x s)). Qed.
Lemma lem5215419 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5215420 (x : real) (s : real -> Prop) : (term302 x s) = (term315 x s).
Proof. exact (MK_COMB (@lem5215419) (@lem5215418 x s)). Qed.
Lemma lem5215421 (x : real) (s : real -> Prop) : ((term301 x s) = (term302 x s)) = ((term300 x s) = (term315 x s)).
Proof. exact (MK_COMB (@lem5215412 x s) (@lem5215420 x s)). Qed.
Lemma lem5215422 (x : real) (s : real -> Prop) : (term300 x s) = (term315 x s).
Proof. exact (EQ_MP (@lem5215421 x s) (@lem5215402 x s)). Qed.
Lemma lem5215424 {A : Type'} (P : Prop) (Q : A -> Prop) : (term316 A P Q) = (term317 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5215425 (P : Prop) (Q : type1028) : (term318 P Q) = (term319 P Q).
Proof. exact (@lem5215424 (real -> real) P Q). Qed.
Lemma lem5215426 (b : real) (x : real) (s : real -> Prop) : (term320 b x s) = (term321 b x s).
Proof. exact (@lem5215425 (term256 b x s) (term298 x s)). Qed.
Lemma lem5215427 (x : real) (s : real -> Prop) (x' : real -> real) : (term322 x s x') = (term296 x s x').
Proof. exact (eq_refl (term322 x s x')). Qed.
Lemma lem5215428 (x : real) (s : real -> Prop) : (term323 x s) = (term298 x s).
Proof. exact (fun_ext (fun x' : real -> real => @lem5215427 x s x')). Qed.
Lemma lem5215429 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5215430 (x : real) (s : real -> Prop) : (term324 x s) = (term299 x s).
Proof. exact (MK_COMB (@lem5215429) (@lem5215428 x s)). Qed.
Lemma lem5215431 (b : real) (x : real) (s : real -> Prop) : (term310 b x s) = (term310 b x s).
Proof. exact (eq_refl (term310 b x s)). Qed.
Lemma lem5215432 (b : real) (x : real) (s : real -> Prop) : (term320 b x s) = (term312 b x s).
Proof. exact (MK_COMB (@lem5215431 b x s) (@lem5215430 x s)). Qed.
Lemma lem5215433 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5215434 (b : real) (x : real) (s : real -> Prop) : (term325 b x s) = (term326 b x s).
Proof. exact (MK_COMB (@lem5215433) (@lem5215432 b x s)). Qed.
Lemma lem5215435 (x : real) (s : real -> Prop) (x' : real -> real) : (term322 x s x') = (term296 x s x').
Proof. exact (eq_refl (term322 x s x')). Qed.
Lemma lem5215436 (b : real) (x : real) (s : real -> Prop) : (term310 b x s) = (term310 b x s).
Proof. exact (eq_refl (term310 b x s)). Qed.
Lemma lem5215437 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) : (term327 b x s x') = (term328 b x s x').
Proof. exact (MK_COMB (@lem5215436 b x s) (@lem5215435 x s x')). Qed.
Lemma lem5215438 (b : real) (x : real) (s : real -> Prop) : (term329 b x s) = (term330 b x s).
Proof. exact (fun_ext (fun x' : real -> real => @lem5215437 b x s x')). Qed.
Lemma lem5215439 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5215440 (b : real) (x : real) (s : real -> Prop) : (term321 b x s) = (term331 b x s).
Proof. exact (MK_COMB (@lem5215439) (@lem5215438 b x s)). Qed.
Lemma lem5215441 (b : real) (x : real) (s : real -> Prop) : ((term320 b x s) = (term321 b x s)) = ((term312 b x s) = (term331 b x s)).
Proof. exact (MK_COMB (@lem5215434 b x s) (@lem5215440 b x s)). Qed.
Lemma lem5215442 (b : real) (x : real) (s : real -> Prop) : (term312 b x s) = (term331 b x s).
Proof. exact (EQ_MP (@lem5215441 b x s) (@lem5215426 b x s)). Qed.
Lemma lem5215443 (x : real) (s : real -> Prop) : (term314 x s) = (term332 x s).
Proof. exact (fun_ext (fun b : real => @lem5215442 b x s)). Qed.
Lemma lem5215444 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5215445 (x : real) (s : real -> Prop) : (term315 x s) = (term333 x s).
Proof. exact (MK_COMB (@lem5215444) (@lem5215443 x s)). Qed.
Lemma lem5215446 (x : real) (s : real -> Prop) : (term300 x s) = (term333 x s).
Proof. exact (TRANS (@lem5215422 x s) (@lem5215445 x s)). Qed.
Lemma lem5215447 (x : real) (s : real -> Prop) : (term206 x s) = (term333 x s).
Proof. exact (TRANS (@lem5215398 x s) (@lem5215446 x s)). Qed.
Lemma lem5215448 (x : real) : (term215 x) = (term334 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5215447 x s)). Qed.
Lemma lem5215449 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5215450 (x : real) : (term216 x) = (term335 x).
Proof. exact (MK_COMB (@lem5215449) (@lem5215448 x)). Qed.
Lemma lem5215451 : term221 = term336.
Proof. exact (fun_ext (fun x : real => @lem5215450 x)). Qed.
Lemma lem5215452 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5215454 : term222 = term337.
Proof. exact (MK_COMB (@lem5215452) (@lem5215451)). Qed.
Lemma lem5215455 : term125 = term337.
Proof. exact (TRANS (@lem5215043) (@lem5215454)). Qed.
Lemma lem5215456 (h1 : term125) : term337.
Proof. exact (EQ_MP (@lem5215455) (@lem5214932 h1)). Qed.
Lemma lem5215463 (x : real) (y : real) (z : real) : (term338 x y z) = (term339 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem5215464 (x : real) (z : real) : (real_le x z) = (real_le x z).
Proof. exact (eq_refl (real_le x z)). Qed.
Lemma lem5215465 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5215466 (x : real) (y : real) (z : real) : (term340 x y z) = (term341 x y z).
Proof. exact (MK_COMB (@lem5215465) (@lem5215463 x y z)). Qed.
Lemma lem5215467 (y : real) (x : real) (z : real) : (term342 y x z) = (term343 y x z).
Proof. exact (MK_COMB (@lem5215466 x y z) (@lem5215464 x z)). Qed.
Lemma lem5215468 (y : real) (x : real) (z : real) : (term142 y x z) = (term342 y x z).
Proof. exact (@lem17265 (term344 x y z) (real_le x z)). Qed.
Lemma lem5215469 (y : real) (x : real) (z : real) : (term142 y x z) = (term343 y x z).
Proof. exact (TRANS (@lem5215468 y x z) (@lem5215467 y x z)). Qed.
Lemma lem5215470 (y : real) (x : real) : (term143 y x) = (term345 y x).
Proof. exact (fun_ext (fun z : real => @lem5215469 y x z)). Qed.
Lemma lem5215471 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215472 (y : real) (x : real) : (term144 y x) = (term346 y x).
Proof. exact (MK_COMB (@lem5215471) (@lem5215470 y x)). Qed.
Lemma lem5215473 (x : real) : (term145 x) = (term347 x).
Proof. exact (fun_ext (fun y : real => @lem5215472 y x)). Qed.
Lemma lem5215474 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215475 (x : real) : (term146 x) = (term348 x).
Proof. exact (MK_COMB (@lem5215474) (@lem5215473 x)). Qed.
Lemma lem5215476 : term147 = term349.
Proof. exact (fun_ext (fun x : real => @lem5215475 x)). Qed.
Lemma lem5215477 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215538 : term148 = term350.
Proof. exact (MK_COMB (@lem5215477) (@lem5215476)). Qed.
Lemma lem5215539 (h1 : term148) : term350.
Proof. exact (EQ_MP (@lem5215538) (@lem5214933 h1)). Qed.
Lemma lem5215544 (y : real) (x : real) : (term138 y x) = (term138 y x).
Proof. exact (eq_refl (term138 y x)). Qed.
Lemma lem5215545 (x : real) : (term139 x) = (term139 x).
Proof. exact (fun_ext (fun y : real => @lem5215544 y x)). Qed.
Lemma lem5215546 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215547 (x : real) : (term140 x) = (term140 x).
Proof. exact (MK_COMB (@lem5215546) (@lem5215545 x)). Qed.
Lemma lem5215548 : term141 = term141.
Proof. exact (fun_ext (fun x : real => @lem5215547 x)). Qed.
Lemma lem5215549 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215606 : term132 = term132.
Proof. exact (MK_COMB (@lem5215549) (@lem5215548)). Qed.
Lemma lem5215607 (h1 : term132) : term132.
Proof. exact (EQ_MP (@lem5215606) (@lem5214934 h1)). Qed.
Lemma lem5215608 (x : real) (h1 : term335 x) : term335 x.
Proof. exact (h1). Qed.
Lemma lem5215609 (x : real) (s : real -> Prop) (h1 : term333 x s) : term333 x s.
Proof. exact (h1). Qed.
Lemma lem5215610 (b : real) (x : real) (s : real -> Prop) (h1 : term331 b x s) : term331 b x s.
Proof. exact (h1). Qed.
Lemma lem5215611 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term328 b x s x'.
Proof. exact (h1). Qed.
Lemma lem5215636 (y : real) (x : real) (z : real) : (term343 y x z) = (term343 y x z).
Proof. exact (eq_refl (term343 y x z)). Qed.
Lemma lem5215637 (y : real) (x : real) : (term345 y x) = (term345 y x).
Proof. exact (fun_ext (fun z : real => @lem5215636 y x z)). Qed.
Lemma lem5215638 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215639 (y : real) (x : real) : (term346 y x) = (term346 y x).
Proof. exact (MK_COMB (@lem5215638) (@lem5215637 y x)). Qed.
Lemma lem5215640 (x : real) : (term347 x) = (term347 x).
Proof. exact (fun_ext (fun y : real => @lem5215639 y x)). Qed.
Lemma lem5215641 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215642 (x : real) : (term348 x) = (term348 x).
Proof. exact (MK_COMB (@lem5215641) (@lem5215640 x)). Qed.
Lemma lem5215643 : term349 = term349.
Proof. exact (fun_ext (fun x : real => @lem5215642 x)). Qed.
Lemma lem5215644 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215645 : term350 = term350.
Proof. exact (MK_COMB (@lem5215644) (@lem5215643)). Qed.
Lemma lem5215646 (h1 : term148) : term350.
Proof. exact (EQ_MP (@lem5215645) (@lem5215539 h1)). Qed.
Lemma lem5215659 (y : real) (x : real) : (term138 y x) = (term138 y x).
Proof. exact (eq_refl (term138 y x)). Qed.
Lemma lem5215660 (x : real) : (term139 x) = (term139 x).
Proof. exact (fun_ext (fun y : real => @lem5215659 y x)). Qed.
Lemma lem5215661 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215662 (x : real) : (term140 x) = (term140 x).
Proof. exact (MK_COMB (@lem5215661) (@lem5215660 x)). Qed.
Lemma lem5215663 : term141 = term141.
Proof. exact (fun_ext (fun x : real => @lem5215662 x)). Qed.
Lemma lem5215664 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215665 : term132 = term132.
Proof. exact (MK_COMB (@lem5215664) (@lem5215663)). Qed.
Lemma lem5215666 (h1 : term132) : term132.
Proof. exact (EQ_MP (@lem5215665) (@lem5215607 h1)). Qed.
Lemma lem5215715 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term292 x s x' b) = (term292 x s x' b).
Proof. exact (eq_refl (term292 x s x' b)). Qed.
Lemma lem5215716 (x : real) (s : real -> Prop) (x' : real -> real) : (term294 x s x') = (term294 x s x').
Proof. exact (fun_ext (fun b : real => @lem5215715 x s x' b)). Qed.
Lemma lem5215717 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215718 (x : real) (s : real -> Prop) (x' : real -> real) : (term296 x s x') = (term296 x s x').
Proof. exact (MK_COMB (@lem5215717) (@lem5215716 x s x')). Qed.
Lemma lem5215731 (x : real) (s : real -> Prop) : (term54 x s) = (term54 x s).
Proof. exact (eq_refl (term54 x s)). Qed.
Lemma lem5215746 (s : real -> Prop) (b : real) (x : real) : (term166 s b x) = (term166 s b x).
Proof. exact (eq_refl (term166 s b x)). Qed.
Lemma lem5215747 (s : real -> Prop) (b : real) : (term167 s b) = (term167 s b).
Proof. exact (fun_ext (fun x : real => @lem5215746 s b x)). Qed.
Lemma lem5215748 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215749 (s : real -> Prop) (b : real) : (term168 s b) = (term168 s b).
Proof. exact (MK_COMB (@lem5215748) (@lem5215747 s b)). Qed.
Lemma lem5215756 (b : real) (s : real -> Prop) : (term152 b s) = (term152 b s).
Proof. exact (eq_refl (term152 b s)). Qed.
Lemma lem5215757 (s : real -> Prop) (b : real) : (term169 s b) = (term169 s b).
Proof. exact (MK_COMB (@lem5215756 b s) (@lem5215749 s b)). Qed.
Lemma lem5215764 (x : real) (s : real -> Prop) : (term162 x s) = (term162 x s).
Proof. exact (eq_refl (term162 x s)). Qed.
Lemma lem5215765 (s : real -> Prop) : (term164 s) = (term164 s).
Proof. exact (fun_ext (fun x : real => @lem5215764 x s)). Qed.
Lemma lem5215766 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215767 (s : real -> Prop) : (term165 s) = (term165 s).
Proof. exact (MK_COMB (@lem5215766) (@lem5215765 s)). Qed.
Lemma lem5215768 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5215769 (s : real -> Prop) : (term173 s) = (term173 s).
Proof. exact (MK_COMB (@lem5215768) (@lem5215767 s)). Qed.
Lemma lem5215770 (s : real -> Prop) (b : real) : (term235 s b) = (term235 s b).
Proof. exact (MK_COMB (@lem5215769 s) (@lem5215757 s b)). Qed.
Lemma lem5215771 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5215772 (s : real -> Prop) (b : real) : (term254 s b) = (term254 s b).
Proof. exact (MK_COMB (@lem5215771) (@lem5215770 s b)). Qed.
Lemma lem5215773 (b : real) (x : real) (s : real -> Prop) : (term256 b x s) = (term256 b x s).
Proof. exact (MK_COMB (@lem5215772 s b) (@lem5215731 x s)). Qed.
Lemma lem5215774 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5215775 (b : real) (x : real) (s : real -> Prop) : (term310 b x s) = (term310 b x s).
Proof. exact (MK_COMB (@lem5215774) (@lem5215773 b x s)). Qed.
Lemma lem5215776 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) : (term328 b x s x') = (term328 b x s x').
Proof. exact (MK_COMB (@lem5215775 b x s) (@lem5215718 x s x')). Qed.
Lemma lem5215777 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term328 b x s x'.
Proof. exact (EQ_MP (@lem5215776 b x s x') (@lem5215611 b x s x' h1)). Qed.
Lemma lem5215778 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term296 x s x'.
Proof. exact (proj2 (@lem5215777 b x s x' h1)). Qed.
Lemma lem5215779 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term256 b x s.
Proof. exact (proj1 (@lem5215777 b x s x' h1)). Qed.
Lemma lem5215781 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term235 s b.
Proof. exact (proj1 (@lem5215779 b x s x' h1)). Qed.
Lemma lem5215784 (s : real -> Prop) (h1 : term165 s) : term165 s.
Proof. exact (h1). Qed.
Lemma lem5215785 (s : real -> Prop) (b : real) (h1 : term169 s b) : term169 s b.
Proof. exact (h1). Qed.
Lemma lem5215786 (s : real -> Prop) (b : real) (h1 : term169 s b) : term168 s b.
Proof. exact (proj2 (@lem5215785 s b h1)). Qed.
Lemma lem5215820 (y : real) (x : real) : (term138 y x) = (term138 y x).
Proof. exact (eq_refl (term138 y x)). Qed.
Lemma lem5215821 (x : real) : (term139 x) = (term139 x).
Proof. exact (fun_ext (fun y : real => @lem5215820 y x)). Qed.
Lemma lem5215822 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215823 (x : real) : (term140 x) = (term140 x).
Proof. exact (MK_COMB (@lem5215822) (@lem5215821 x)). Qed.
Lemma lem5215824 : term141 = term141.
Proof. exact (fun_ext (fun x : real => @lem5215823 x)). Qed.
Lemma lem5215825 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215827 : term132 = term132.
Proof. exact (MK_COMB (@lem5215825) (@lem5215824)). Qed.
Lemma lem5215828 (h1 : term132) : term132.
Proof. exact (EQ_MP (@lem5215827) (@lem5215666 h1)). Qed.
Lemma lem5215849 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term292 x s x' b) = (term351 x s x' b).
Proof. exact (@lem19490 (term352 x x' b s) (term179 x b s) (term353 x' b)). Qed.
Lemma lem5215856 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term354 x s x' b) = (term355 x s x' b).
Proof. exact (@lem19699 (term356 b x) (term162 b s) (term353 x' b)). Qed.
Lemma lem5215863 (x : real) (x' : real -> real) (b : real) (s : real -> Prop) : (term357 x x' b s) = (term358 x x' b s).
Proof. exact (@lem19699 (term356 b x) (term162 b s) (term352 x x' b s)). Qed.
Lemma lem5215864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5215865 (x : real) (x' : real -> real) (b : real) (s : real -> Prop) : (term359 x x' b s) = (term360 x x' b s).
Proof. exact (MK_COMB (@lem5215864) (@lem5215863 x x' b s)). Qed.
Lemma lem5215866 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term351 x s x' b) = (term361 x s x' b).
Proof. exact (MK_COMB (@lem5215865 x x' b s) (@lem5215856 x s x' b)). Qed.
Lemma lem5215868 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term292 x s x' b) = (term361 x s x' b).
Proof. exact (TRANS (@lem5215849 x s x' b) (@lem5215866 x s x' b)). Qed.
Lemma lem5215869 (x : real) (s : real -> Prop) (x' : real -> real) : (term294 x s x') = (term362 x s x').
Proof. exact (fun_ext (fun b : real => @lem5215868 x s x' b)). Qed.
Lemma lem5215870 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215872 (x : real) (s : real -> Prop) (x' : real -> real) : (term296 x s x') = (term363 x s x').
Proof. exact (MK_COMB (@lem5215870) (@lem5215869 x s x')). Qed.
Lemma lem5215873 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term363 x s x'.
Proof. exact (EQ_MP (@lem5215872 x s x') (@lem5215778 b x s x' h1)). Qed.
Lemma lem5215883 (x : real) (s : real -> Prop) : (term162 x s) = (term162 x s).
Proof. exact (eq_refl (term162 x s)). Qed.
Lemma lem5215884 (s : real -> Prop) : (term164 s) = (term164 s).
Proof. exact (fun_ext (fun x : real => @lem5215883 x s)). Qed.
Lemma lem5215885 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215887 (s : real -> Prop) : (term165 s) = (term165 s).
Proof. exact (MK_COMB (@lem5215885) (@lem5215884 s)). Qed.
Lemma lem5215888 (s : real -> Prop) (h1 : term165 s) : term165 s.
Proof. exact (EQ_MP (@lem5215887 s) (@lem5215784 s h1)). Qed.
Lemma lem5215902 (y : real) (x : real) (z : real) : (term343 y x z) = (term343 y x z).
Proof. exact (eq_refl (term343 y x z)). Qed.
Lemma lem5215903 (y : real) (x : real) : (term345 y x) = (term345 y x).
Proof. exact (fun_ext (fun z : real => @lem5215902 y x z)). Qed.
Lemma lem5215904 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215905 (y : real) (x : real) : (term346 y x) = (term346 y x).
Proof. exact (MK_COMB (@lem5215904) (@lem5215903 y x)). Qed.
Lemma lem5215906 (x : real) : (term347 x) = (term347 x).
Proof. exact (fun_ext (fun y : real => @lem5215905 y x)). Qed.
Lemma lem5215907 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215908 (x : real) : (term348 x) = (term348 x).
Proof. exact (MK_COMB (@lem5215907) (@lem5215906 x)). Qed.
Lemma lem5215909 : term349 = term349.
Proof. exact (fun_ext (fun x : real => @lem5215908 x)). Qed.
Lemma lem5215910 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215912 : term350 = term350.
Proof. exact (MK_COMB (@lem5215910) (@lem5215909)). Qed.
Lemma lem5215913 (h1 : term148) : term350.
Proof. exact (EQ_MP (@lem5215912) (@lem5215646 h1)). Qed.
Lemma lem5215921 (y : real) (x : real) : (term138 y x) = (term138 y x).
Proof. exact (eq_refl (term138 y x)). Qed.
Lemma lem5215922 (x : real) : (term139 x) = (term139 x).
Proof. exact (fun_ext (fun y : real => @lem5215921 y x)). Qed.
Lemma lem5215923 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215924 (x : real) : (term140 x) = (term140 x).
Proof. exact (MK_COMB (@lem5215923) (@lem5215922 x)). Qed.
Lemma lem5215925 : term141 = term141.
Proof. exact (fun_ext (fun x : real => @lem5215924 x)). Qed.
Lemma lem5215926 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215928 : term132 = term132.
Proof. exact (MK_COMB (@lem5215926) (@lem5215925)). Qed.
Lemma lem5215929 (h1 : term132) : term132.
Proof. exact (EQ_MP (@lem5215928) (@lem5215666 h1)). Qed.
Lemma lem5215950 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term292 x s x' b) = (term351 x s x' b).
Proof. exact (@lem19490 (term352 x x' b s) (term179 x b s) (term353 x' b)). Qed.
Lemma lem5215957 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term354 x s x' b) = (term355 x s x' b).
Proof. exact (@lem19699 (term356 b x) (term162 b s) (term353 x' b)). Qed.
Lemma lem5215964 (x : real) (x' : real -> real) (b : real) (s : real -> Prop) : (term357 x x' b s) = (term358 x x' b s).
Proof. exact (@lem19699 (term356 b x) (term162 b s) (term352 x x' b s)). Qed.
Lemma lem5215965 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5215966 (x : real) (x' : real -> real) (b : real) (s : real -> Prop) : (term359 x x' b s) = (term360 x x' b s).
Proof. exact (MK_COMB (@lem5215965) (@lem5215964 x x' b s)). Qed.
Lemma lem5215967 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term351 x s x' b) = (term361 x s x' b).
Proof. exact (MK_COMB (@lem5215966 x x' b s) (@lem5215957 x s x' b)). Qed.
Lemma lem5215969 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term292 x s x' b) = (term361 x s x' b).
Proof. exact (TRANS (@lem5215950 x s x' b) (@lem5215967 x s x' b)). Qed.
Lemma lem5215970 (x : real) (s : real -> Prop) (x' : real -> real) : (term294 x s x') = (term362 x s x').
Proof. exact (fun_ext (fun b : real => @lem5215969 x s x' b)). Qed.
Lemma lem5215971 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215973 (x : real) (s : real -> Prop) (x' : real -> real) : (term296 x s x') = (term363 x s x').
Proof. exact (MK_COMB (@lem5215971) (@lem5215970 x s x')). Qed.
Lemma lem5215974 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term363 x s x'.
Proof. exact (EQ_MP (@lem5215973 x s x') (@lem5215778 b x s x' h1)). Qed.
Lemma lem5215994 (s : real -> Prop) (b : real) (x : real) : (term166 s b x) = (term166 s b x).
Proof. exact (eq_refl (term166 s b x)). Qed.
Lemma lem5215995 (s : real -> Prop) (b : real) : (term167 s b) = (term167 s b).
Proof. exact (fun_ext (fun x : real => @lem5215994 s b x)). Qed.
Lemma lem5215996 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5215998 (s : real -> Prop) (b : real) : (term168 s b) = (term168 s b).
Proof. exact (MK_COMB (@lem5215996) (@lem5215995 s b)). Qed.
Lemma lem5215999 (s : real -> Prop) (b : real) (h1 : term169 s b) : term168 s b.
Proof. exact (EQ_MP (@lem5215998 s b) (@lem5215786 s b h1)). Qed.
Lemma lem5216009 (_68271 : real) (h1 : term132) : term364 _68271.
Proof. exact (@lem5215828 h1 _68271). Qed.
Lemma lem5216010 (_68271 : real) : (term364 _68271) = (term140 _68271).
Proof. exact (eq_refl (term364 _68271)). Qed.
Lemma lem5216011 (_68271 : real) (h1 : term132) : term140 _68271.
Proof. exact (EQ_MP (@lem5216010 _68271) (@lem5216009 _68271 h1)). Qed.
Lemma lem5216012 (_68271 : real) (_68272 : real) (h1 : term132) : term365 _68271 _68272.
Proof. exact (@lem5216011 _68271 h1 _68272). Qed.
Lemma lem5216013 (_68272 : real) (_68271 : real) : (term365 _68271 _68272) = (term138 _68272 _68271).
Proof. exact (eq_refl (term365 _68271 _68272)). Qed.
Lemma lem5216015 (_68273 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term366 x s x' _68273.
Proof. exact (@lem5215873 b x s x' h1 _68273). Qed.
Lemma lem5216016 (x : real) (s : real -> Prop) (x' : real -> real) (_68273 : real) : (term366 x s x' _68273) = (term361 x s x' _68273).
Proof. exact (eq_refl (term366 x s x' _68273)). Qed.
Lemma lem5216017 (_68273 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term361 x s x' _68273.
Proof. exact (EQ_MP (@lem5216016 x s x' _68273) (@lem5216015 _68273 b x s x' h1)). Qed.
Lemma lem5216018 (_68274 : real) (s : real -> Prop) (h1 : term165 s) : term367 s _68274.
Proof. exact (@lem5215888 s h1 _68274). Qed.
Lemma lem5216019 (_68274 : real) (s : real -> Prop) : (term367 s _68274) = (term162 _68274 s).
Proof. exact (eq_refl (term367 s _68274)). Qed.
Lemma lem5216021 (_68275 : real) (h1 : term148) : term368 _68275.
Proof. exact (@lem5215913 h1 _68275). Qed.
Lemma lem5216022 (_68275 : real) : (term368 _68275) = (term348 _68275).
Proof. exact (eq_refl (term368 _68275)). Qed.
Lemma lem5216023 (_68275 : real) (h1 : term148) : term348 _68275.
Proof. exact (EQ_MP (@lem5216022 _68275) (@lem5216021 _68275 h1)). Qed.
Lemma lem5216024 (_68275 : real) (_68276 : real) (h1 : term148) : term369 _68275 _68276.
Proof. exact (@lem5216023 _68275 h1 _68276). Qed.
Lemma lem5216025 (_68276 : real) (_68275 : real) : (term369 _68275 _68276) = (term346 _68276 _68275).
Proof. exact (eq_refl (term369 _68275 _68276)). Qed.
Lemma lem5216026 (_68276 : real) (_68275 : real) (h1 : term148) : term346 _68276 _68275.
Proof. exact (EQ_MP (@lem5216025 _68276 _68275) (@lem5216024 _68275 _68276 h1)). Qed.
Lemma lem5216027 (_68276 : real) (_68275 : real) (_68277 : real) (h1 : term148) : term370 _68276 _68275 _68277.
Proof. exact (@lem5216026 _68276 _68275 h1 _68277). Qed.
Lemma lem5216028 (_68276 : real) (_68275 : real) (_68277 : real) : (term370 _68276 _68275 _68277) = (term343 _68276 _68275 _68277).
Proof. exact (eq_refl (term370 _68276 _68275 _68277)). Qed.
Lemma lem5216029 (_68276 : real) (_68275 : real) (_68277 : real) (h1 : term148) : term343 _68276 _68275 _68277.
Proof. exact (EQ_MP (@lem5216028 _68276 _68275 _68277) (@lem5216027 _68276 _68275 _68277 h1)). Qed.
Lemma lem5216030 (_68278 : real) (h1 : term132) : term364 _68278.
Proof. exact (@lem5215929 h1 _68278). Qed.
Lemma lem5216031 (_68278 : real) : (term364 _68278) = (term140 _68278).
Proof. exact (eq_refl (term364 _68278)). Qed.
Lemma lem5216032 (_68278 : real) (h1 : term132) : term140 _68278.
Proof. exact (EQ_MP (@lem5216031 _68278) (@lem5216030 _68278 h1)). Qed.
Lemma lem5216033 (_68278 : real) (_68279 : real) (h1 : term132) : term365 _68278 _68279.
Proof. exact (@lem5216032 _68278 h1 _68279). Qed.
Lemma lem5216034 (_68279 : real) (_68278 : real) : (term365 _68278 _68279) = (term138 _68279 _68278).
Proof. exact (eq_refl (term365 _68278 _68279)). Qed.
Lemma lem5216036 (_68280 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term366 x s x' _68280.
Proof. exact (@lem5215974 b x s x' h1 _68280). Qed.
Lemma lem5216037 (x : real) (s : real -> Prop) (x' : real -> real) (_68280 : real) : (term366 x s x' _68280) = (term361 x s x' _68280).
Proof. exact (eq_refl (term366 x s x' _68280)). Qed.
Lemma lem5216038 (_68280 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term361 x s x' _68280.
Proof. exact (EQ_MP (@lem5216037 x s x' _68280) (@lem5216036 _68280 b x s x' h1)). Qed.
Lemma lem5216039 (_68281 : real) (s : real -> Prop) (b : real) (h1 : term169 s b) : term371 s b _68281.
Proof. exact (@lem5215999 s b h1 _68281). Qed.
Lemma lem5216040 (s : real -> Prop) (b : real) (_68281 : real) : (term371 s b _68281) = (term166 s b _68281).
Proof. exact (eq_refl (term371 s b _68281)). Qed.
Lemma lem5216042 (_68273 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term355 x s x' _68273.
Proof. exact (proj2 (@lem5216017 _68273 b x s x' h1)). Qed.
Lemma lem5216043 (_68273 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term358 x x' _68273 s.
Proof. exact (proj1 (@lem5216017 _68273 b x s x' h1)). Qed.
Lemma lem5216048 (_68280 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term355 x s x' _68280.
Proof. exact (proj2 (@lem5216038 _68280 b x s x' h1)). Qed.
Lemma lem5216049 (_68280 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term358 x x' _68280 s.
Proof. exact (proj1 (@lem5216038 _68280 b x s x' h1)). Qed.
Lemma lem5216071 (_68272 : real) (_68271 : real) (h1 : term132) : term138 _68272 _68271.
Proof. exact (EQ_MP (@lem5216013 _68272 _68271) (@lem5216012 _68271 _68272 h1)). Qed.
Lemma lem5216083 (_68273 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term372 x x' _68273.
Proof. exact (proj1 (@lem5216042 _68273 b x s x' h1)). Qed.
Lemma lem5216099 (_68273 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term373 x x' _68273 s.
Proof. exact (proj1 (@lem5216043 _68273 b x s x' h1)). Qed.
Lemma lem5216120 (_68276 : real) (_68275 : real) (_68277 : real) : (term343 _68276 _68275 _68277) = (term374 _68276 _68275 _68277).
Proof. exact (@lem5214037 (term375 _68275 _68276) (term375 _68276 _68277) (real_le _68275 _68277)). Qed.
Lemma lem5216121 (_68276 : real) (_68275 : real) (_68277 : real) (h1 : term148) : term374 _68276 _68275 _68277.
Proof. exact (EQ_MP (@lem5216120 _68276 _68275 _68277) (@lem5216029 _68276 _68275 _68277 h1)). Qed.
Lemma lem5216127 (_68279 : real) (_68278 : real) (h1 : term132) : term138 _68279 _68278.
Proof. exact (EQ_MP (@lem5216034 _68279 _68278) (@lem5216033 _68278 _68279 h1)). Qed.
Lemma lem5216139 (_68281 : real) (s : real -> Prop) (b : real) (h1 : term169 s b) : term166 s b _68281.
Proof. exact (EQ_MP (@lem5216040 s b _68281) (@lem5216039 _68281 s b h1)). Qed.
Lemma lem5216145 (_68280 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term372 x x' _68280.
Proof. exact (proj1 (@lem5216048 _68280 b x s x' h1)). Qed.
Lemma lem5216151 (_68280 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term376 s x' _68280.
Proof. exact (proj2 (@lem5216048 _68280 b x s x' h1)). Qed.
Lemma lem5216161 (_68280 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term373 x x' _68280 s.
Proof. exact (proj1 (@lem5216049 _68280 b x s x' h1)). Qed.
Lemma lem5216171 (_68280 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term377 x x' _68280 s.
Proof. exact (proj2 (@lem5216049 _68280 b x s x' h1)). Qed.
Lemma lem5216203 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5216204 (_68288 : real) (_68290 : real) (h1 : _68288 = _68290) : _68288 = _68290.
Proof. exact (h1). Qed.
Lemma lem5216205 (_68289 : real) (_68291 : real) (h1 : _68289 = _68291) : _68289 = _68291.
Proof. exact (h1). Qed.
Lemma lem5216206 (_68288 : real) (_68290 : real) (h1 : _68288 = _68290) : (real_le _68288) = (real_le _68290).
Proof. exact (MK_COMB (@lem5216203) (@lem5216204 _68288 _68290 h1)). Qed.
Lemma lem5216207 (_68288 : real) (_68290 : real) (_68289 : real) (_68291 : real) (h1 : _68288 = _68290) (h2 : _68289 = _68291) : (real_le _68288 _68289) = (real_le _68290 _68291).
Proof. exact (MK_COMB (@lem5216206 _68288 _68290 h1) (@lem5216205 _68289 _68291 h2)). Qed.
Lemma lem5216209 (b : Prop) (a : Prop) : term378 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5216210 (_68290 : real) (_68291 : real) (_68288 : real) (_68289 : real) : term379 _68290 _68291 _68288 _68289.
Proof. exact (@lem5216209 (real_le _68290 _68291) (real_le _68288 _68289)). Qed.
Lemma lem5216211 (_68288 : real) (_68290 : real) (_68289 : real) (_68291 : real) (h1 : _68288 = _68290) (h2 : _68289 = _68291) : term380 _68290 _68291 _68288 _68289.
Proof. exact (@lem5216210 _68290 _68291 _68288 _68289 (@lem5216207 _68288 _68290 _68289 _68291 h1 h2)). Qed.
Lemma lem5216212 (_68291 : real) (_68289 : real) (_68288 : real) (_68290 : real) (h1 : _68288 = _68290) : term381 _68290 _68291 _68288 _68289.
Proof. exact (fun h0 : _68289 = _68291 => @lem5216211 _68288 _68290 _68289 _68291 h1 h0). Qed.
Lemma lem5216214 (a : Prop) (b : Prop) : (a -> b) = (term382 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5216215 (_68290 : real) (_68291 : real) (_68288 : real) (_68289 : real) : (term381 _68290 _68291 _68288 _68289) = (term383 _68290 _68291 _68288 _68289).
Proof. exact (@lem5216214 (_68289 = _68291) (term380 _68290 _68291 _68288 _68289)). Qed.
Lemma lem5216216 (_68291 : real) (_68289 : real) (_68288 : real) (_68290 : real) (h1 : _68288 = _68290) : term383 _68290 _68291 _68288 _68289.
Proof. exact (EQ_MP (@lem5216215 _68290 _68291 _68288 _68289) (@lem5216212 _68291 _68289 _68288 _68290 h1)). Qed.
Lemma lem5216217 (_68290 : real) (_68291 : real) (_68288 : real) (_68289 : real) : term384 _68290 _68291 _68288 _68289.
Proof. exact (fun h0 : _68288 = _68290 => @lem5216216 _68291 _68289 _68288 _68290 h0). Qed.
Lemma lem5216219 (a : Prop) (b : Prop) : (a -> b) = (term382 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5216220 (_68290 : real) (_68291 : real) (_68288 : real) (_68289 : real) : (term384 _68290 _68291 _68288 _68289) = (term385 _68290 _68291 _68288 _68289).
Proof. exact (@lem5216219 (_68288 = _68290) (term383 _68290 _68291 _68288 _68289)). Qed.
Lemma lem5216221 (_68290 : real) (_68291 : real) (_68288 : real) (_68289 : real) : term385 _68290 _68291 _68288 _68289.
Proof. exact (EQ_MP (@lem5216220 _68290 _68291 _68288 _68289) (@lem5216217 _68290 _68291 _68288 _68289)). Qed.
Lemma lem5216235 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5216236 (x : real) : term386 x.
Proof. exact (fun h0 : term387 x => @lem5216235 x). Qed.
Lemma lem5216238 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5216239 (x : real) : (term386 x) = (x = x).
Proof. exact (@lem5216238 (x = x)). Qed.
Lemma lem5216240 (x : real) : x = x.
Proof. exact (EQ_MP (@lem5216239 x) (@lem5216236 x)). Qed.
Lemma lem5216242 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5216243 (x : real) : term386 x.
Proof. exact (fun h0 : term387 x => @lem5216242 x). Qed.
Lemma lem5216245 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5216246 (x : real) : (term386 x) = (x = x).
Proof. exact (@lem5216245 (x = x)). Qed.
Lemma lem5216247 (x : real) : x = x.
Proof. exact (EQ_MP (@lem5216246 x) (@lem5216243 x)). Qed.
Lemma lem5216249 (_68274 : real) (s : real -> Prop) (h1 : term165 s) : term162 _68274 s.
Proof. exact (EQ_MP (@lem5216019 _68274 s) (@lem5216018 _68274 s h1)). Qed.
Lemma lem5216250 (x' : real -> real) (x : real) (s : real -> Prop) (h1 : term165 s) : term389 x' x s.
Proof. exact (@lem5216249 (x' x) s h1). Qed.
Lemma lem5216251 (x' : real -> real) (x : real) (s : real -> Prop) (h1 : term165 s) : term390 x' x s.
Proof. exact (fun h0 : term391 x' x s => @lem5216250 x' x s h1). Qed.
Lemma lem5216253 (p : Prop) : (term392 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5216254 (x' : real -> real) (x : real) (s : real -> Prop) : (term390 x' x s) = (term389 x' x s).
Proof. exact (@lem5216253 (term391 x' x s)). Qed.
Lemma lem5216255 (x' : real -> real) (x : real) (s : real -> Prop) (h1 : term165 s) : term389 x' x s.
Proof. exact (EQ_MP (@lem5216254 x' x s) (@lem5216251 x' x s h1)). Qed.
Lemma lem5216261 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5216262 (x : real) (x' : real -> real) (_68273 : real) (s : real -> Prop) : (term373 x x' _68273 s) = (term393 x x' _68273 s).
Proof. exact (@lem5216261 ((x' _68273) = x) (term356 _68273 x) (term391 x' _68273 s)). Qed.
Lemma lem5216278 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5216279 (x' : real -> real) (s : real -> Prop) (_68273 : real) (x : real) : (term394 x x' _68273 s) = (term395 x' s _68273 x).
Proof. exact (@lem5216278 (term391 x' _68273 s) (term356 _68273 x)). Qed.
Lemma lem5216287 (x' : real -> real) (_68273 : real) (x : real) : (term396 x' _68273 x) = (term396 x' _68273 x).
Proof. exact (eq_refl (term396 x' _68273 x)). Qed.
Lemma lem5216288 (x' : real -> real) (s : real -> Prop) (_68273 : real) (x : real) : (term393 x x' _68273 s) = (term397 x' s _68273 x).
Proof. exact (MK_COMB (@lem5216287 x' _68273 x) (@lem5216279 x' s _68273 x)). Qed.
Lemma lem5216299 (x' : real -> real) (s : real -> Prop) (_68273 : real) (x : real) : (term373 x x' _68273 s) = (term397 x' s _68273 x).
Proof. exact (TRANS (@lem5216262 x x' _68273 s) (@lem5216288 x' s _68273 x)). Qed.
Lemma lem5216300 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5216301 (x' : real -> real) (s : real -> Prop) (_68273 : real) (x : real) : (term398 x x' _68273 s) = (term399 x' s _68273 x).
Proof. exact (MK_COMB (@lem5216300) (@lem5216299 x' s _68273 x)). Qed.
Lemma lem5216317 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5216318 (x' : real -> real) (s : real -> Prop) (_68273 : real) (x : real) : (term394 x x' _68273 s) = (term395 x' s _68273 x).
Proof. exact (@lem5216317 (term391 x' _68273 s) (term356 _68273 x)). Qed.
Lemma lem5216326 (x' : real -> real) (_68273 : real) (x : real) : (term396 x' _68273 x) = (term396 x' _68273 x).
Proof. exact (eq_refl (term396 x' _68273 x)). Qed.
Lemma lem5216327 (x' : real -> real) (s : real -> Prop) (_68273 : real) (x : real) : (term393 x x' _68273 s) = (term397 x' s _68273 x).
Proof. exact (MK_COMB (@lem5216326 x' _68273 x) (@lem5216318 x' s _68273 x)). Qed.
Lemma lem5216338 (x' : real -> real) (s : real -> Prop) (_68273 : real) (x : real) : ((term373 x x' _68273 s) = (term393 x x' _68273 s)) = ((term397 x' s _68273 x) = (term397 x' s _68273 x)).
Proof. exact (MK_COMB (@lem5216301 x' s _68273 x) (@lem5216327 x' s _68273 x)). Qed.
Lemma lem5216340 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5216341 (x : Prop) : (x = x) = True.
Proof. exact (@lem5216340 Prop x). Qed.
Lemma lem5216342 (x' : real -> real) (s : real -> Prop) (_68273 : real) (x : real) : ((term397 x' s _68273 x) = (term397 x' s _68273 x)) = True.
Proof. exact (@lem5216341 (term397 x' s _68273 x)). Qed.
Lemma lem5216343 (x : real) (x' : real -> real) (_68273 : real) (s : real -> Prop) : ((term373 x x' _68273 s) = (term393 x x' _68273 s)) = True.
Proof. exact (TRANS (@lem5216338 x' s _68273 x) (@lem5216342 x' s _68273 x)). Qed.
Lemma lem5216344 (x : real) (x' : real -> real) (_68273 : real) (s : real -> Prop) : True = ((term373 x x' _68273 s) = (term393 x x' _68273 s)).
Proof. exact (SYM (@lem5216343 x x' _68273 s)). Qed.
Lemma lem5216345 (x : real) (x' : real -> real) (_68273 : real) (s : real -> Prop) : (term373 x x' _68273 s) = (term393 x x' _68273 s).
Proof. exact (EQ_MP (@lem5216344 x x' _68273 s) (@lem0)). Qed.
Lemma lem5216346 (_68273 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term393 x x' _68273 s.
Proof. exact (EQ_MP (@lem5216345 x x' _68273 s) (@lem5216099 _68273 b x s x' h1)). Qed.
Lemma lem5216348 (b : Prop) (a : Prop) : (a \/ b) = (term400 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5216349 (s : real -> Prop) (x' : real -> real) (_68273 : real) (x : real) : (term393 x x' _68273 s) = (term401 s x' _68273 x).
Proof. exact (@lem5216348 (term394 x x' _68273 s) ((x' _68273) = x)). Qed.
Lemma lem5216351 (a : Prop) (b : Prop) : (term402 a b) = (term403 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5216352 (x : real) (x' : real -> real) (_68273 : real) (s : real -> Prop) : (term404 x x' _68273 s) = (term405 x x' _68273 s).
Proof. exact (@lem5216351 (term356 _68273 x) (term391 x' _68273 s)). Qed.
Lemma lem5216354 (a : Prop) : (term406 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5216355 (_68273 : real) (x : real) : (term407 _68273 x) = (_68273 = x).
Proof. exact (@lem5216354 (_68273 = x)). Qed.
Lemma lem5216356 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5216357 (_68273 : real) (x : real) : (term408 _68273 x) = (term409 _68273 x).
Proof. exact (MK_COMB (@lem5216356) (@lem5216355 _68273 x)). Qed.
Lemma lem5216358 (x' : real -> real) (_68273 : real) (s : real -> Prop) : (term389 x' _68273 s) = (term389 x' _68273 s).
Proof. exact (eq_refl (term389 x' _68273 s)). Qed.
Lemma lem5216359 (x : real) (x' : real -> real) (_68273 : real) (s : real -> Prop) : (term405 x x' _68273 s) = (term410 x x' _68273 s).
Proof. exact (MK_COMB (@lem5216357 _68273 x) (@lem5216358 x' _68273 s)). Qed.
Lemma lem5216360 (x : real) (x' : real -> real) (_68273 : real) (s : real -> Prop) : (term404 x x' _68273 s) = (term410 x x' _68273 s).
Proof. exact (TRANS (@lem5216352 x x' _68273 s) (@lem5216359 x x' _68273 s)). Qed.
Lemma lem5216361 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5216362 (x : real) (x' : real -> real) (_68273 : real) (s : real -> Prop) : (term411 x x' _68273 s) = (term412 x x' _68273 s).
Proof. exact (MK_COMB (@lem5216361) (@lem5216360 x x' _68273 s)). Qed.
Lemma lem5216363 (x' : real -> real) (_68273 : real) (x : real) : ((x' _68273) = x) = ((x' _68273) = x).
Proof. exact (eq_refl ((x' _68273) = x)). Qed.
Lemma lem5216364 (s : real -> Prop) (x' : real -> real) (_68273 : real) (x : real) : (term401 s x' _68273 x) = (term413 s x' _68273 x).
Proof. exact (MK_COMB (@lem5216362 x x' _68273 s) (@lem5216363 x' _68273 x)). Qed.
Lemma lem5216365 (s : real -> Prop) (x' : real -> real) (_68273 : real) (x : real) : (term393 x x' _68273 s) = (term413 s x' _68273 x).
Proof. exact (TRANS (@lem5216349 s x' _68273 x) (@lem5216364 s x' _68273 x)). Qed.
Lemma lem5216367 (x' : real -> real) (x : real) (s : real -> Prop) (h1 : term165 s) : term414 x' x s.
Proof. exact (conj (@lem5216247 x) (@lem5216255 x' x s h1)). Qed.
Lemma lem5216369 (_68273 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term413 s x' _68273 x.
Proof. exact (EQ_MP (@lem5216365 s x' _68273 x) (@lem5216346 _68273 b x s x' h1)). Qed.
Lemma lem5216370 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term415 s x' x.
Proof. exact (@lem5216369 x b x s x' h1). Qed.
Lemma lem5216373 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term165 s) (h2 : term328 b x s x') : (x' x) = x.
Proof. exact (@lem5216370 b x s x' h2 (@lem5216367 x' x s h1)). Qed.
Lemma lem5216374 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term165 s) (h2 : term328 b x s x') : term416 x' x.
Proof. exact (fun h0 : term417 x' x => @lem5216373 b x s x' h1 h2). Qed.
Lemma lem5216376 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5216377 (x' : real -> real) (x : real) : (term416 x' x) = ((x' x) = x).
Proof. exact (@lem5216376 ((x' x) = x)). Qed.
Lemma lem5216378 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term165 s) (h2 : term328 b x s x') : (x' x) = x.
Proof. exact (EQ_MP (@lem5216377 x' x) (@lem5216374 b x s x' h1 h2)). Qed.
Lemma lem5216380 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5216381 (x' : real -> real) (x : real) : (x' x) = (x' x).
Proof. exact (@lem5216380 (x' x)). Qed.
Lemma lem5216382 (x' : real -> real) (x : real) : term418 x' x.
Proof. exact (fun h0 : term419 x' x => @lem5216381 x' x). Qed.
Lemma lem5216384 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5216385 (x' : real -> real) (x : real) : (term418 x' x) = ((x' x) = (x' x)).
Proof. exact (@lem5216384 ((x' x) = (x' x))). Qed.
Lemma lem5216386 (x' : real -> real) (x : real) : (x' x) = (x' x).
Proof. exact (EQ_MP (@lem5216385 x' x) (@lem5216382 x' x)). Qed.
Lemma lem5216389 (x' : real -> real) (x : real) (h1 : term420 x' x) : term420 x' x.
Proof. exact (h1). Qed.
Lemma lem5216390 (x' : real -> real) (x : real) (h1 : term420 x' x) : term421 x' x.
Proof. exact (fun h0 : term422 x' x => @lem5216389 x' x h1). Qed.
Lemma lem5216392 (p : Prop) : (term392 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5216393 (x' : real -> real) (x : real) : (term421 x' x) = (term420 x' x).
Proof. exact (@lem5216392 (term422 x' x)). Qed.
Lemma lem5216394 (x' : real -> real) (x : real) (h1 : term420 x' x) : term420 x' x.
Proof. exact (EQ_MP (@lem5216393 x' x) (@lem5216390 x' x h1)). Qed.
Lemma lem5216405 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5216406 (_68272 : real) (_68271 : real) : (term138 _68271 _68272) = (term138 _68272 _68271).
Proof. exact (@lem5216405 (real_le _68271 _68272) (real_le _68272 _68271)). Qed.
Lemma lem5216412 (_68272 : real) (_68271 : real) : (term423 _68272 _68271) = (term423 _68272 _68271).
Proof. exact (eq_refl (term423 _68272 _68271)). Qed.
Lemma lem5216413 (_68272 : real) (_68271 : real) : ((term138 _68272 _68271) = (term138 _68271 _68272)) = ((term138 _68272 _68271) = (term138 _68272 _68271)).
Proof. exact (MK_COMB (@lem5216412 _68272 _68271) (@lem5216406 _68272 _68271)). Qed.
Lemma lem5216415 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5216416 (x : Prop) : (x = x) = True.
Proof. exact (@lem5216415 Prop x). Qed.
Lemma lem5216417 (_68272 : real) (_68271 : real) : ((term138 _68272 _68271) = (term138 _68272 _68271)) = True.
Proof. exact (@lem5216416 (term138 _68272 _68271)). Qed.
Lemma lem5216418 (_68271 : real) (_68272 : real) : ((term138 _68272 _68271) = (term138 _68271 _68272)) = True.
Proof. exact (TRANS (@lem5216413 _68272 _68271) (@lem5216417 _68272 _68271)). Qed.
Lemma lem5216419 (_68271 : real) (_68272 : real) : True = ((term138 _68272 _68271) = (term138 _68271 _68272)).
Proof. exact (SYM (@lem5216418 _68271 _68272)). Qed.
Lemma lem5216420 (_68271 : real) (_68272 : real) : (term138 _68272 _68271) = (term138 _68271 _68272).
Proof. exact (EQ_MP (@lem5216419 _68271 _68272) (@lem0)). Qed.
Lemma lem5216421 (_68271 : real) (_68272 : real) (h1 : term132) : term138 _68271 _68272.
Proof. exact (EQ_MP (@lem5216420 _68271 _68272) (@lem5216071 _68272 _68271 h1)). Qed.
Lemma lem5216423 (b : Prop) (a : Prop) : (a \/ b) = (term400 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5216426 (_68272 : real) (_68271 : real) : (term138 _68271 _68272) = (term424 _68272 _68271).
Proof. exact (@lem5216423 (real_le _68271 _68272) (real_le _68272 _68271)). Qed.
Lemma lem5216429 (_68272 : real) (_68271 : real) (h1 : term132) : term424 _68272 _68271.
Proof. exact (EQ_MP (@lem5216426 _68272 _68271) (@lem5216421 _68271 _68272 h1)). Qed.
Lemma lem5216430 (x' : real -> real) (x : real) (h1 : term132) : term425 x' x.
Proof. exact (@lem5216429 (x' x) (x' x) h1). Qed.
Lemma lem5216433 (x' : real -> real) (x : real) (h1 : term132) (h2 : term420 x' x) : term422 x' x.
Proof. exact (@lem5216430 x' x h1 (@lem5216394 x' x h2)). Qed.
Lemma lem5216434 (x' : real -> real) (x : real) (h1 : term132) : term425 x' x.
Proof. exact (fun h0 : term420 x' x => @lem5216433 x' x h1 h0). Qed.
Lemma lem5216436 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5216437 (x' : real -> real) (x : real) : (term425 x' x) = (term422 x' x).
Proof. exact (@lem5216436 (term422 x' x)). Qed.
Lemma lem5216438 (x' : real -> real) (x : real) (h1 : term132) : term422 x' x.
Proof. exact (EQ_MP (@lem5216437 x' x) (@lem5216434 x' x h1)). Qed.
Lemma lem5216456 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5216457 (_68290 : real) (_68291 : real) (_68288 : real) (_68289 : real) : (term383 _68290 _68291 _68288 _68289) = (term426 _68290 _68291 _68288 _68289).
Proof. exact (@lem5216456 (real_le _68290 _68291) (term356 _68289 _68291) (term375 _68288 _68289)). Qed.
Lemma lem5216475 (_68288 : real) (_68290 : real) : (term427 _68288 _68290) = (term427 _68288 _68290).
Proof. exact (eq_refl (term427 _68288 _68290)). Qed.
Lemma lem5216476 (_68290 : real) (_68291 : real) (_68288 : real) (_68289 : real) : (term385 _68290 _68291 _68288 _68289) = (term428 _68290 _68291 _68288 _68289).
Proof. exact (MK_COMB (@lem5216475 _68288 _68290) (@lem5216457 _68290 _68291 _68288 _68289)). Qed.
Lemma lem5216480 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5216481 (_68290 : real) (_68291 : real) (_68288 : real) (_68289 : real) : (term428 _68290 _68291 _68288 _68289) = (term429 _68290 _68291 _68288 _68289).
Proof. exact (@lem5216480 (real_le _68290 _68291) (term356 _68288 _68290) (term430 _68291 _68288 _68289)). Qed.
Lemma lem5216511 (_68290 : real) (_68291 : real) (_68288 : real) (_68289 : real) : (term385 _68290 _68291 _68288 _68289) = (term429 _68290 _68291 _68288 _68289).
Proof. exact (TRANS (@lem5216476 _68290 _68291 _68288 _68289) (@lem5216481 _68290 _68291 _68288 _68289)). Qed.
Lemma lem5216512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5216513 (_68290 : real) (_68291 : real) (_68288 : real) (_68289 : real) : (term431 _68290 _68291 _68288 _68289) = (term432 _68290 _68291 _68288 _68289).
Proof. exact (MK_COMB (@lem5216512) (@lem5216511 _68290 _68291 _68288 _68289)). Qed.
Lemma lem5216543 (_68290 : real) (_68291 : real) (_68288 : real) (_68289 : real) : (term429 _68290 _68291 _68288 _68289) = (term429 _68290 _68291 _68288 _68289).
Proof. exact (eq_refl (term429 _68290 _68291 _68288 _68289)). Qed.
Lemma lem5216544 (_68290 : real) (_68291 : real) (_68288 : real) (_68289 : real) : ((term385 _68290 _68291 _68288 _68289) = (term429 _68290 _68291 _68288 _68289)) = ((term429 _68290 _68291 _68288 _68289) = (term429 _68290 _68291 _68288 _68289)).
Proof. exact (MK_COMB (@lem5216513 _68290 _68291 _68288 _68289) (@lem5216543 _68290 _68291 _68288 _68289)). Qed.
Lemma lem5216546 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5216547 (x : Prop) : (x = x) = True.
Proof. exact (@lem5216546 Prop x). Qed.
Lemma lem5216548 (_68290 : real) (_68291 : real) (_68288 : real) (_68289 : real) : ((term429 _68290 _68291 _68288 _68289) = (term429 _68290 _68291 _68288 _68289)) = True.
Proof. exact (@lem5216547 (term429 _68290 _68291 _68288 _68289)). Qed.
Lemma lem5216549 (_68290 : real) (_68291 : real) (_68288 : real) (_68289 : real) : ((term385 _68290 _68291 _68288 _68289) = (term429 _68290 _68291 _68288 _68289)) = True.
Proof. exact (TRANS (@lem5216544 _68290 _68291 _68288 _68289) (@lem5216548 _68290 _68291 _68288 _68289)). Qed.
Lemma lem5216550 (_68290 : real) (_68291 : real) (_68288 : real) (_68289 : real) : True = ((term385 _68290 _68291 _68288 _68289) = (term429 _68290 _68291 _68288 _68289)).
Proof. exact (SYM (@lem5216549 _68290 _68291 _68288 _68289)). Qed.
Lemma lem5216551 (_68290 : real) (_68291 : real) (_68288 : real) (_68289 : real) : (term385 _68290 _68291 _68288 _68289) = (term429 _68290 _68291 _68288 _68289).
Proof. exact (EQ_MP (@lem5216550 _68290 _68291 _68288 _68289) (@lem0)). Qed.
Lemma lem5216552 (_68290 : real) (_68291 : real) (_68288 : real) (_68289 : real) : term429 _68290 _68291 _68288 _68289.
Proof. exact (EQ_MP (@lem5216551 _68290 _68291 _68288 _68289) (@lem5216221 _68290 _68291 _68288 _68289)). Qed.
Lemma lem5216554 (b : Prop) (a : Prop) : (a \/ b) = (term400 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5216555 (_68288 : real) (_68289 : real) (_68290 : real) (_68291 : real) : (term429 _68290 _68291 _68288 _68289) = (term433 _68288 _68289 _68290 _68291).
Proof. exact (@lem5216554 (term434 _68290 _68291 _68288 _68289) (real_le _68290 _68291)). Qed.
Lemma lem5216557 (a : Prop) (b : Prop) : (term402 a b) = (term403 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5216558 (_68290 : real) (_68291 : real) (_68288 : real) (_68289 : real) : (term435 _68290 _68291 _68288 _68289) = (term436 _68290 _68291 _68288 _68289).
Proof. exact (@lem5216557 (term356 _68288 _68290) (term430 _68291 _68288 _68289)). Qed.
Lemma lem5216560 (a : Prop) : (term406 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5216561 (_68288 : real) (_68290 : real) : (term407 _68288 _68290) = (_68288 = _68290).
Proof. exact (@lem5216560 (_68288 = _68290)). Qed.
Lemma lem5216562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5216563 (_68288 : real) (_68290 : real) : (term408 _68288 _68290) = (term409 _68288 _68290).
Proof. exact (MK_COMB (@lem5216562) (@lem5216561 _68288 _68290)). Qed.
Lemma lem5216565 (a : Prop) (b : Prop) : (term402 a b) = (term403 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5216566 (_68291 : real) (_68288 : real) (_68289 : real) : (term437 _68291 _68288 _68289) = (term438 _68291 _68288 _68289).
Proof. exact (@lem5216565 (term356 _68289 _68291) (term375 _68288 _68289)). Qed.
Lemma lem5216568 (a : Prop) : (term406 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5216569 (_68289 : real) (_68291 : real) : (term407 _68289 _68291) = (_68289 = _68291).
Proof. exact (@lem5216568 (_68289 = _68291)). Qed.
Lemma lem5216570 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5216571 (_68289 : real) (_68291 : real) : (term408 _68289 _68291) = (term409 _68289 _68291).
Proof. exact (MK_COMB (@lem5216570) (@lem5216569 _68289 _68291)). Qed.
Lemma lem5216573 (a : Prop) : (term406 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5216574 (_68288 : real) (_68289 : real) : (term439 _68288 _68289) = (real_le _68288 _68289).
Proof. exact (@lem5216573 (real_le _68288 _68289)). Qed.
Lemma lem5216575 (_68291 : real) (_68288 : real) (_68289 : real) : (term438 _68291 _68288 _68289) = (term440 _68291 _68288 _68289).
Proof. exact (MK_COMB (@lem5216571 _68289 _68291) (@lem5216574 _68288 _68289)). Qed.
Lemma lem5216576 (_68291 : real) (_68288 : real) (_68289 : real) : (term437 _68291 _68288 _68289) = (term440 _68291 _68288 _68289).
Proof. exact (TRANS (@lem5216566 _68291 _68288 _68289) (@lem5216575 _68291 _68288 _68289)). Qed.
Lemma lem5216577 (_68290 : real) (_68291 : real) (_68288 : real) (_68289 : real) : (term436 _68290 _68291 _68288 _68289) = (term441 _68290 _68291 _68288 _68289).
Proof. exact (MK_COMB (@lem5216563 _68288 _68290) (@lem5216576 _68291 _68288 _68289)). Qed.
Lemma lem5216578 (_68290 : real) (_68291 : real) (_68288 : real) (_68289 : real) : (term435 _68290 _68291 _68288 _68289) = (term441 _68290 _68291 _68288 _68289).
Proof. exact (TRANS (@lem5216558 _68290 _68291 _68288 _68289) (@lem5216577 _68290 _68291 _68288 _68289)). Qed.
Lemma lem5216579 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5216580 (_68290 : real) (_68291 : real) (_68288 : real) (_68289 : real) : (term442 _68290 _68291 _68288 _68289) = (term443 _68290 _68291 _68288 _68289).
Proof. exact (MK_COMB (@lem5216579) (@lem5216578 _68290 _68291 _68288 _68289)). Qed.
Lemma lem5216581 (_68290 : real) (_68291 : real) : (real_le _68290 _68291) = (real_le _68290 _68291).
Proof. exact (eq_refl (real_le _68290 _68291)). Qed.
Lemma lem5216582 (_68288 : real) (_68289 : real) (_68290 : real) (_68291 : real) : (term433 _68288 _68289 _68290 _68291) = (term444 _68288 _68289 _68290 _68291).
Proof. exact (MK_COMB (@lem5216580 _68290 _68291 _68288 _68289) (@lem5216581 _68290 _68291)). Qed.
Lemma lem5216583 (_68288 : real) (_68289 : real) (_68290 : real) (_68291 : real) : (term429 _68290 _68291 _68288 _68289) = (term444 _68288 _68289 _68290 _68291).
Proof. exact (TRANS (@lem5216555 _68288 _68289 _68290 _68291) (@lem5216582 _68288 _68289 _68290 _68291)). Qed.
Lemma lem5216585 (x' : real -> real) (x : real) (h1 : term132) : term445 x' x.
Proof. exact (conj (@lem5216386 x' x) (@lem5216438 x' x h1)). Qed.
Lemma lem5216586 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : term446 x' x.
Proof. exact (conj (@lem5216378 b x s x' h2 h3) (@lem5216585 x' x h1)). Qed.
Lemma lem5216588 (_68288 : real) (_68289 : real) (_68290 : real) (_68291 : real) : term444 _68288 _68289 _68290 _68291.
Proof. exact (EQ_MP (@lem5216583 _68288 _68289 _68290 _68291) (@lem5216552 _68290 _68291 _68288 _68289)). Qed.
Lemma lem5216589 (x' : real -> real) (x : real) : term447 x' x.
Proof. exact (@lem5216588 (x' x) (x' x) x (x' x)). Qed.
Lemma lem5216592 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : term448 x' x.
Proof. exact (@lem5216589 x' x (@lem5216586 b x s x' h1 h2 h3)). Qed.
Lemma lem5216593 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : term449 x' x.
Proof. exact (fun h0 : term353 x' x => @lem5216592 b x s x' h1 h2 h3). Qed.
Lemma lem5216595 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5216596 (x' : real -> real) (x : real) : (term449 x' x) = (term448 x' x).
Proof. exact (@lem5216595 (term448 x' x)). Qed.
Lemma lem5216597 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : term448 x' x.
Proof. exact (EQ_MP (@lem5216596 x' x) (@lem5216593 b x s x' h1 h2 h3)). Qed.
Lemma lem5216599 (a : Prop) (b : Prop) : (term450 a b) = (term451 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5216600 (x : real) (x' : real -> real) (_68273 : real) : (term372 x x' _68273) = (term452 x x' _68273).
Proof. exact (@lem5216599 (_68273 = x) (term448 x' _68273)). Qed.
Lemma lem5216602 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5216603 (x : real) (x' : real -> real) (_68273 : real) : (term452 x x' _68273) = (term453 x x' _68273).
Proof. exact (@lem5216602 (term454 x x' _68273)). Qed.
Lemma lem5216604 (x : real) (x' : real -> real) (_68273 : real) : (term372 x x' _68273) = (term453 x x' _68273).
Proof. exact (TRANS (@lem5216600 x x' _68273) (@lem5216603 x x' _68273)). Qed.
Lemma lem5216606 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : term455 x' x.
Proof. exact (conj (@lem5216240 x) (@lem5216597 b x s x' h1 h2 h3)). Qed.
Lemma lem5216608 (_68273 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term453 x x' _68273.
Proof. exact (EQ_MP (@lem5216604 x x' _68273) (@lem5216083 _68273 b x s x' h1)). Qed.
Lemma lem5216609 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term456 x' x.
Proof. exact (@lem5216608 x b x s x' h1). Qed.
Lemma lem5216612 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : False.
Proof. exact (@lem5216609 b x s x' h3 (@lem5216606 b x s x' h1 h2 h3)). Qed.
Lemma lem5216613 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : term457.
Proof. exact (fun h0 : ~ False => @lem5216612 b x s x' h1 h2 h3). Qed.
Lemma lem5216615 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5216616 : term457 = False.
Proof. exact (@lem5216615 False). Qed.
Lemma lem5216617 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : False.
Proof. exact (EQ_MP (@lem5216616) (@lem5216613 b x s x' h1 h2 h3)). Qed.
Lemma lem5216649 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5216650 (_68300 : real) (_68302 : real) (h1 : _68300 = _68302) : _68300 = _68302.
Proof. exact (h1). Qed.
Lemma lem5216651 (_68301 : real) (_68303 : real) (h1 : _68301 = _68303) : _68301 = _68303.
Proof. exact (h1). Qed.
Lemma lem5216652 (_68300 : real) (_68302 : real) (h1 : _68300 = _68302) : (real_le _68300) = (real_le _68302).
Proof. exact (MK_COMB (@lem5216649) (@lem5216650 _68300 _68302 h1)). Qed.
Lemma lem5216653 (_68300 : real) (_68302 : real) (_68301 : real) (_68303 : real) (h1 : _68300 = _68302) (h2 : _68301 = _68303) : (real_le _68300 _68301) = (real_le _68302 _68303).
Proof. exact (MK_COMB (@lem5216652 _68300 _68302 h1) (@lem5216651 _68301 _68303 h2)). Qed.
Lemma lem5216655 (b : Prop) (a : Prop) : term378 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5216656 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : term379 _68302 _68303 _68300 _68301.
Proof. exact (@lem5216655 (real_le _68302 _68303) (real_le _68300 _68301)). Qed.
Lemma lem5216657 (_68300 : real) (_68302 : real) (_68301 : real) (_68303 : real) (h1 : _68300 = _68302) (h2 : _68301 = _68303) : term380 _68302 _68303 _68300 _68301.
Proof. exact (@lem5216656 _68302 _68303 _68300 _68301 (@lem5216653 _68300 _68302 _68301 _68303 h1 h2)). Qed.
Lemma lem5216658 (_68303 : real) (_68301 : real) (_68300 : real) (_68302 : real) (h1 : _68300 = _68302) : term381 _68302 _68303 _68300 _68301.
Proof. exact (fun h0 : _68301 = _68303 => @lem5216657 _68300 _68302 _68301 _68303 h1 h0). Qed.
Lemma lem5216660 (a : Prop) (b : Prop) : (a -> b) = (term382 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5216661 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : (term381 _68302 _68303 _68300 _68301) = (term383 _68302 _68303 _68300 _68301).
Proof. exact (@lem5216660 (_68301 = _68303) (term380 _68302 _68303 _68300 _68301)). Qed.
Lemma lem5216662 (_68303 : real) (_68301 : real) (_68300 : real) (_68302 : real) (h1 : _68300 = _68302) : term383 _68302 _68303 _68300 _68301.
Proof. exact (EQ_MP (@lem5216661 _68302 _68303 _68300 _68301) (@lem5216658 _68303 _68301 _68300 _68302 h1)). Qed.
Lemma lem5216663 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : term384 _68302 _68303 _68300 _68301.
Proof. exact (fun h0 : _68300 = _68302 => @lem5216662 _68303 _68301 _68300 _68302 h0). Qed.
Lemma lem5216665 (a : Prop) (b : Prop) : (a -> b) = (term382 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5216666 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : (term384 _68302 _68303 _68300 _68301) = (term385 _68302 _68303 _68300 _68301).
Proof. exact (@lem5216665 (_68300 = _68302) (term383 _68302 _68303 _68300 _68301)). Qed.
Lemma lem5216667 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : term385 _68302 _68303 _68300 _68301.
Proof. exact (EQ_MP (@lem5216666 _68302 _68303 _68300 _68301) (@lem5216663 _68302 _68303 _68300 _68301)). Qed.
Lemma lem5216681 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5216682 (x : real) : term386 x.
Proof. exact (fun h0 : term387 x => @lem5216681 x). Qed.
Lemma lem5216684 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5216685 (x : real) : (term386 x) = (x = x).
Proof. exact (@lem5216684 (x = x)). Qed.
Lemma lem5216686 (x : real) : x = x.
Proof. exact (EQ_MP (@lem5216685 x) (@lem5216682 x)). Qed.
Lemma lem5216688 (s : real -> Prop) (b : real) (h1 : term169 s b) : @IN real b s.
Proof. exact (proj1 (@lem5215785 s b h1)). Qed.
Lemma lem5216689 (s : real -> Prop) (b : real) (h1 : term169 s b) : term458 b s.
Proof. exact (fun h0 : term162 b s => @lem5216688 s b h1). Qed.
Lemma lem5216691 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5216692 (b : real) (s : real -> Prop) : (term458 b s) = (@IN real b s).
Proof. exact (@lem5216691 (@IN real b s)). Qed.
Lemma lem5216693 (s : real -> Prop) (b : real) (h1 : term169 s b) : @IN real b s.
Proof. exact (EQ_MP (@lem5216692 b s) (@lem5216689 s b h1)). Qed.
Lemma lem5216695 (s : real -> Prop) (b : real) (h1 : term169 s b) : @IN real b s.
Proof. exact (proj1 (@lem5215785 s b h1)). Qed.
Lemma lem5216696 (s : real -> Prop) (b : real) (h1 : term169 s b) : term458 b s.
Proof. exact (fun h0 : term162 b s => @lem5216695 s b h1). Qed.
Lemma lem5216698 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5216699 (b : real) (s : real -> Prop) : (term458 b s) = (@IN real b s).
Proof. exact (@lem5216698 (@IN real b s)). Qed.
Lemma lem5216700 (s : real -> Prop) (b : real) (h1 : term169 s b) : @IN real b s.
Proof. exact (EQ_MP (@lem5216699 b s) (@lem5216696 s b h1)). Qed.
Lemma lem5216711 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5216712 (s : real -> Prop) (x' : real -> real) (_68280 : real) : (term459 x' _68280 s) = (term376 s x' _68280).
Proof. exact (@lem5216711 (term162 _68280 s) (term353 x' _68280)). Qed.
Lemma lem5216718 (s : real -> Prop) (x' : real -> real) (_68280 : real) : (term460 s x' _68280) = (term460 s x' _68280).
Proof. exact (eq_refl (term460 s x' _68280)). Qed.
Lemma lem5216719 (s : real -> Prop) (x' : real -> real) (_68280 : real) : ((term376 s x' _68280) = (term459 x' _68280 s)) = ((term376 s x' _68280) = (term376 s x' _68280)).
Proof. exact (MK_COMB (@lem5216718 s x' _68280) (@lem5216712 s x' _68280)). Qed.
Lemma lem5216721 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5216722 (x : Prop) : (x = x) = True.
Proof. exact (@lem5216721 Prop x). Qed.
Lemma lem5216723 (s : real -> Prop) (x' : real -> real) (_68280 : real) : ((term376 s x' _68280) = (term376 s x' _68280)) = True.
Proof. exact (@lem5216722 (term376 s x' _68280)). Qed.
Lemma lem5216724 (x' : real -> real) (_68280 : real) (s : real -> Prop) : ((term376 s x' _68280) = (term459 x' _68280 s)) = True.
Proof. exact (TRANS (@lem5216719 s x' _68280) (@lem5216723 s x' _68280)). Qed.
Lemma lem5216725 (x' : real -> real) (_68280 : real) (s : real -> Prop) : True = ((term376 s x' _68280) = (term459 x' _68280 s)).
Proof. exact (SYM (@lem5216724 x' _68280 s)). Qed.
Lemma lem5216726 (x' : real -> real) (_68280 : real) (s : real -> Prop) : (term376 s x' _68280) = (term459 x' _68280 s).
Proof. exact (EQ_MP (@lem5216725 x' _68280 s) (@lem0)). Qed.
Lemma lem5216727 (_68280 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term459 x' _68280 s.
Proof. exact (EQ_MP (@lem5216726 x' _68280 s) (@lem5216151 _68280 b x s x' h1)). Qed.
Lemma lem5216729 (b : Prop) (a : Prop) : (a \/ b) = (term400 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5216730 (s : real -> Prop) (x' : real -> real) (_68280 : real) : (term459 x' _68280 s) = (term461 s x' _68280).
Proof. exact (@lem5216729 (term162 _68280 s) (term353 x' _68280)). Qed.
Lemma lem5216732 (a : Prop) : (term406 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5216733 (_68280 : real) (s : real -> Prop) : (term462 _68280 s) = (@IN real _68280 s).
Proof. exact (@lem5216732 (@IN real _68280 s)). Qed.
Lemma lem5216734 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5216735 (_68280 : real) (s : real -> Prop) : (term463 _68280 s) = (term464 _68280 s).
Proof. exact (MK_COMB (@lem5216734) (@lem5216733 _68280 s)). Qed.
Lemma lem5216736 (x' : real -> real) (_68280 : real) : (term353 x' _68280) = (term353 x' _68280).
Proof. exact (eq_refl (term353 x' _68280)). Qed.
Lemma lem5216737 (s : real -> Prop) (x' : real -> real) (_68280 : real) : (term461 s x' _68280) = (term465 s x' _68280).
Proof. exact (MK_COMB (@lem5216735 _68280 s) (@lem5216736 x' _68280)). Qed.
Lemma lem5216738 (s : real -> Prop) (x' : real -> real) (_68280 : real) : (term459 x' _68280 s) = (term465 s x' _68280).
Proof. exact (TRANS (@lem5216730 s x' _68280) (@lem5216737 s x' _68280)). Qed.
Lemma lem5216741 (_68280 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term465 s x' _68280.
Proof. exact (EQ_MP (@lem5216738 s x' _68280) (@lem5216727 _68280 b x s x' h1)). Qed.
Lemma lem5216742 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term465 s x' b.
Proof. exact (@lem5216741 b b x s x' h1). Qed.
Lemma lem5216745 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term353 x' b.
Proof. exact (@lem5216742 b x s x' h1 (@lem5216700 s b h2)). Qed.
Lemma lem5216746 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term466 x' b.
Proof. exact (fun h0 : term448 x' b => @lem5216745 x x' s b h1 h2). Qed.
Lemma lem5216748 (p : Prop) : (term392 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5216749 (x' : real -> real) (b : real) : (term466 x' b) = (term353 x' b).
Proof. exact (@lem5216748 (term448 x' b)). Qed.
Lemma lem5216750 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term353 x' b.
Proof. exact (EQ_MP (@lem5216749 x' b) (@lem5216746 x x' s b h1 h2)). Qed.
Lemma lem5216752 (b : Prop) (a : Prop) : (a \/ b) = (term400 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5216755 (b : real) (_68281 : real) (s : real -> Prop) : (term166 s b _68281) = (term467 b _68281 s).
Proof. exact (@lem5216752 (real_le b _68281) (term162 _68281 s)). Qed.
Lemma lem5216758 (_68281 : real) (s : real -> Prop) (b : real) (h1 : term169 s b) : term467 b _68281 s.
Proof. exact (EQ_MP (@lem5216755 b _68281 s) (@lem5216139 _68281 s b h1)). Qed.
Lemma lem5216759 (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term169 s b) : term468 x' b s.
Proof. exact (@lem5216758 (x' b) s b h1). Qed.
Lemma lem5216762 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term389 x' b s.
Proof. exact (@lem5216759 x' s b h2 (@lem5216750 x x' s b h1 h2)). Qed.
Lemma lem5216763 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term390 x' b s.
Proof. exact (fun h0 : term391 x' b s => @lem5216762 x x' s b h1 h2). Qed.
Lemma lem5216765 (p : Prop) : (term392 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5216766 (x' : real -> real) (b : real) (s : real -> Prop) : (term390 x' b s) = (term389 x' b s).
Proof. exact (@lem5216765 (term391 x' b s)). Qed.
Lemma lem5216767 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term389 x' b s.
Proof. exact (EQ_MP (@lem5216766 x' b s) (@lem5216763 x x' s b h1 h2)). Qed.
Lemma lem5216773 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5216774 (x : real) (x' : real -> real) (_68280 : real) (s : real -> Prop) : (term377 x x' _68280 s) = (term469 x x' _68280 s).
Proof. exact (@lem5216773 ((x' _68280) = x) (term162 _68280 s) (term391 x' _68280 s)). Qed.
Lemma lem5216790 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5216791 (x' : real -> real) (_68280 : real) (s : real -> Prop) : (term470 x' _68280 s) = (term471 x' _68280 s).
Proof. exact (@lem5216790 (term391 x' _68280 s) (term162 _68280 s)). Qed.
Lemma lem5216797 (x' : real -> real) (_68280 : real) (x : real) : (term396 x' _68280 x) = (term396 x' _68280 x).
Proof. exact (eq_refl (term396 x' _68280 x)). Qed.
Lemma lem5216798 (x : real) (x' : real -> real) (_68280 : real) (s : real -> Prop) : (term469 x x' _68280 s) = (term472 x x' _68280 s).
Proof. exact (MK_COMB (@lem5216797 x' _68280 x) (@lem5216791 x' _68280 s)). Qed.
Lemma lem5216809 (x : real) (x' : real -> real) (_68280 : real) (s : real -> Prop) : (term377 x x' _68280 s) = (term472 x x' _68280 s).
Proof. exact (TRANS (@lem5216774 x x' _68280 s) (@lem5216798 x x' _68280 s)). Qed.
Lemma lem5216810 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5216811 (x : real) (x' : real -> real) (_68280 : real) (s : real -> Prop) : (term473 x x' _68280 s) = (term474 x x' _68280 s).
Proof. exact (MK_COMB (@lem5216810) (@lem5216809 x x' _68280 s)). Qed.
Lemma lem5216827 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5216828 (x' : real -> real) (_68280 : real) (s : real -> Prop) : (term470 x' _68280 s) = (term471 x' _68280 s).
Proof. exact (@lem5216827 (term391 x' _68280 s) (term162 _68280 s)). Qed.
Lemma lem5216834 (x' : real -> real) (_68280 : real) (x : real) : (term396 x' _68280 x) = (term396 x' _68280 x).
Proof. exact (eq_refl (term396 x' _68280 x)). Qed.
Lemma lem5216835 (x : real) (x' : real -> real) (_68280 : real) (s : real -> Prop) : (term469 x x' _68280 s) = (term472 x x' _68280 s).
Proof. exact (MK_COMB (@lem5216834 x' _68280 x) (@lem5216828 x' _68280 s)). Qed.
Lemma lem5216846 (x : real) (x' : real -> real) (_68280 : real) (s : real -> Prop) : ((term377 x x' _68280 s) = (term469 x x' _68280 s)) = ((term472 x x' _68280 s) = (term472 x x' _68280 s)).
Proof. exact (MK_COMB (@lem5216811 x x' _68280 s) (@lem5216835 x x' _68280 s)). Qed.
Lemma lem5216848 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5216849 (x : Prop) : (x = x) = True.
Proof. exact (@lem5216848 Prop x). Qed.
Lemma lem5216850 (x : real) (x' : real -> real) (_68280 : real) (s : real -> Prop) : ((term472 x x' _68280 s) = (term472 x x' _68280 s)) = True.
Proof. exact (@lem5216849 (term472 x x' _68280 s)). Qed.
Lemma lem5216851 (x : real) (x' : real -> real) (_68280 : real) (s : real -> Prop) : ((term377 x x' _68280 s) = (term469 x x' _68280 s)) = True.
Proof. exact (TRANS (@lem5216846 x x' _68280 s) (@lem5216850 x x' _68280 s)). Qed.
Lemma lem5216852 (x : real) (x' : real -> real) (_68280 : real) (s : real -> Prop) : True = ((term377 x x' _68280 s) = (term469 x x' _68280 s)).
Proof. exact (SYM (@lem5216851 x x' _68280 s)). Qed.
Lemma lem5216853 (x : real) (x' : real -> real) (_68280 : real) (s : real -> Prop) : (term377 x x' _68280 s) = (term469 x x' _68280 s).
Proof. exact (EQ_MP (@lem5216852 x x' _68280 s) (@lem0)). Qed.
Lemma lem5216854 (_68280 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term469 x x' _68280 s.
Proof. exact (EQ_MP (@lem5216853 x x' _68280 s) (@lem5216171 _68280 b x s x' h1)). Qed.
Lemma lem5216856 (b : Prop) (a : Prop) : (a \/ b) = (term400 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5216857 (s : real -> Prop) (x' : real -> real) (_68280 : real) (x : real) : (term469 x x' _68280 s) = (term475 s x' _68280 x).
Proof. exact (@lem5216856 (term470 x' _68280 s) ((x' _68280) = x)). Qed.
Lemma lem5216859 (a : Prop) (b : Prop) : (term402 a b) = (term403 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5216860 (x' : real -> real) (_68280 : real) (s : real -> Prop) : (term476 x' _68280 s) = (term477 x' _68280 s).
Proof. exact (@lem5216859 (term162 _68280 s) (term391 x' _68280 s)). Qed.
Lemma lem5216862 (a : Prop) : (term406 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5216863 (_68280 : real) (s : real -> Prop) : (term462 _68280 s) = (@IN real _68280 s).
Proof. exact (@lem5216862 (@IN real _68280 s)). Qed.
Lemma lem5216864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5216865 (_68280 : real) (s : real -> Prop) : (term478 _68280 s) = (term152 _68280 s).
Proof. exact (MK_COMB (@lem5216864) (@lem5216863 _68280 s)). Qed.
Lemma lem5216866 (x' : real -> real) (_68280 : real) (s : real -> Prop) : (term389 x' _68280 s) = (term389 x' _68280 s).
Proof. exact (eq_refl (term389 x' _68280 s)). Qed.
Lemma lem5216867 (x' : real -> real) (_68280 : real) (s : real -> Prop) : (term477 x' _68280 s) = (term479 x' _68280 s).
Proof. exact (MK_COMB (@lem5216865 _68280 s) (@lem5216866 x' _68280 s)). Qed.
Lemma lem5216868 (x' : real -> real) (_68280 : real) (s : real -> Prop) : (term476 x' _68280 s) = (term479 x' _68280 s).
Proof. exact (TRANS (@lem5216860 x' _68280 s) (@lem5216867 x' _68280 s)). Qed.
Lemma lem5216869 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5216870 (x' : real -> real) (_68280 : real) (s : real -> Prop) : (term480 x' _68280 s) = (term481 x' _68280 s).
Proof. exact (MK_COMB (@lem5216869) (@lem5216868 x' _68280 s)). Qed.
Lemma lem5216871 (x' : real -> real) (_68280 : real) (x : real) : ((x' _68280) = x) = ((x' _68280) = x).
Proof. exact (eq_refl ((x' _68280) = x)). Qed.
Lemma lem5216872 (s : real -> Prop) (x' : real -> real) (_68280 : real) (x : real) : (term475 s x' _68280 x) = (term482 s x' _68280 x).
Proof. exact (MK_COMB (@lem5216870 x' _68280 s) (@lem5216871 x' _68280 x)). Qed.
Lemma lem5216873 (s : real -> Prop) (x' : real -> real) (_68280 : real) (x : real) : (term469 x x' _68280 s) = (term482 s x' _68280 x).
Proof. exact (TRANS (@lem5216857 s x' _68280 x) (@lem5216872 s x' _68280 x)). Qed.
Lemma lem5216875 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term479 x' b s.
Proof. exact (conj (@lem5216693 s b h2) (@lem5216767 x x' s b h1 h2)). Qed.
Lemma lem5216877 (_68280 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term482 s x' _68280 x.
Proof. exact (EQ_MP (@lem5216873 s x' _68280 x) (@lem5216854 _68280 b x s x' h1)). Qed.
Lemma lem5216878 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term482 s x' b x.
Proof. exact (@lem5216877 b b x s x' h1). Qed.
Lemma lem5216881 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : (x' b) = x.
Proof. exact (@lem5216878 b x s x' h1 (@lem5216875 x x' s b h1 h2)). Qed.
Lemma lem5216882 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term483 x' b x.
Proof. exact (fun h0 : term484 x' b x => @lem5216881 x x' s b h1 h2). Qed.
Lemma lem5216884 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5216885 (x' : real -> real) (b : real) (x : real) : (term483 x' b x) = ((x' b) = x).
Proof. exact (@lem5216884 ((x' b) = x)). Qed.
Lemma lem5216886 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : (x' b) = x.
Proof. exact (EQ_MP (@lem5216885 x' b x) (@lem5216882 x x' s b h1 h2)). Qed.
Lemma lem5216888 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5216889 (x' : real -> real) (x : real) : (x' x) = (x' x).
Proof. exact (@lem5216888 (x' x)). Qed.
Lemma lem5216890 (x' : real -> real) (x : real) : term418 x' x.
Proof. exact (fun h0 : term419 x' x => @lem5216889 x' x). Qed.
Lemma lem5216892 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5216893 (x' : real -> real) (x : real) : (term418 x' x) = ((x' x) = (x' x)).
Proof. exact (@lem5216892 ((x' x) = (x' x))). Qed.
Lemma lem5216894 (x' : real -> real) (x : real) : (x' x) = (x' x).
Proof. exact (EQ_MP (@lem5216893 x' x) (@lem5216890 x' x)). Qed.
Lemma lem5216896 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5216897 (x : real) : term386 x.
Proof. exact (fun h0 : term387 x => @lem5216896 x). Qed.
Lemma lem5216899 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5216900 (x : real) : (term386 x) = (x = x).
Proof. exact (@lem5216899 (x = x)). Qed.
Lemma lem5216901 (x : real) : x = x.
Proof. exact (EQ_MP (@lem5216900 x) (@lem5216897 x)). Qed.
Lemma lem5216903 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5216904 (x' : real -> real) (x : real) : (x' x) = (x' x).
Proof. exact (@lem5216903 (x' x)). Qed.
Lemma lem5216905 (x' : real -> real) (x : real) : term418 x' x.
Proof. exact (fun h0 : term419 x' x => @lem5216904 x' x). Qed.
Lemma lem5216907 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5216908 (x' : real -> real) (x : real) : (term418 x' x) = ((x' x) = (x' x)).
Proof. exact (@lem5216907 ((x' x) = (x' x))). Qed.
Lemma lem5216909 (x' : real -> real) (x : real) : (x' x) = (x' x).
Proof. exact (EQ_MP (@lem5216908 x' x) (@lem5216905 x' x)). Qed.
Lemma lem5216912 (x' : real -> real) (x : real) (h1 : term353 x' x) : term353 x' x.
Proof. exact (h1). Qed.
Lemma lem5216913 (x' : real -> real) (x : real) (h1 : term353 x' x) : term466 x' x.
Proof. exact (fun h0 : term448 x' x => @lem5216912 x' x h1). Qed.
Lemma lem5216915 (p : Prop) : (term392 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5216916 (x' : real -> real) (x : real) : (term466 x' x) = (term353 x' x).
Proof. exact (@lem5216915 (term448 x' x)). Qed.
Lemma lem5216917 (x' : real -> real) (x : real) (h1 : term353 x' x) : term353 x' x.
Proof. exact (EQ_MP (@lem5216916 x' x) (@lem5216913 x' x h1)). Qed.
Lemma lem5216920 (x' : real -> real) (x : real) (h1 : term420 x' x) : term420 x' x.
Proof. exact (h1). Qed.
Lemma lem5216921 (x' : real -> real) (x : real) (h1 : term420 x' x) : term421 x' x.
Proof. exact (fun h0 : term422 x' x => @lem5216920 x' x h1). Qed.
Lemma lem5216923 (p : Prop) : (term392 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5216924 (x' : real -> real) (x : real) : (term421 x' x) = (term420 x' x).
Proof. exact (@lem5216923 (term422 x' x)). Qed.
Lemma lem5216925 (x' : real -> real) (x : real) (h1 : term420 x' x) : term420 x' x.
Proof. exact (EQ_MP (@lem5216924 x' x) (@lem5216921 x' x h1)). Qed.
Lemma lem5216936 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5216937 (_68279 : real) (_68278 : real) : (term138 _68278 _68279) = (term138 _68279 _68278).
Proof. exact (@lem5216936 (real_le _68278 _68279) (real_le _68279 _68278)). Qed.
Lemma lem5216943 (_68279 : real) (_68278 : real) : (term423 _68279 _68278) = (term423 _68279 _68278).
Proof. exact (eq_refl (term423 _68279 _68278)). Qed.
Lemma lem5216944 (_68279 : real) (_68278 : real) : ((term138 _68279 _68278) = (term138 _68278 _68279)) = ((term138 _68279 _68278) = (term138 _68279 _68278)).
Proof. exact (MK_COMB (@lem5216943 _68279 _68278) (@lem5216937 _68279 _68278)). Qed.
Lemma lem5216946 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5216947 (x : Prop) : (x = x) = True.
Proof. exact (@lem5216946 Prop x). Qed.
Lemma lem5216948 (_68279 : real) (_68278 : real) : ((term138 _68279 _68278) = (term138 _68279 _68278)) = True.
Proof. exact (@lem5216947 (term138 _68279 _68278)). Qed.
Lemma lem5216949 (_68278 : real) (_68279 : real) : ((term138 _68279 _68278) = (term138 _68278 _68279)) = True.
Proof. exact (TRANS (@lem5216944 _68279 _68278) (@lem5216948 _68279 _68278)). Qed.
Lemma lem5216950 (_68278 : real) (_68279 : real) : True = ((term138 _68279 _68278) = (term138 _68278 _68279)).
Proof. exact (SYM (@lem5216949 _68278 _68279)). Qed.
Lemma lem5216951 (_68278 : real) (_68279 : real) : (term138 _68279 _68278) = (term138 _68278 _68279).
Proof. exact (EQ_MP (@lem5216950 _68278 _68279) (@lem0)). Qed.
Lemma lem5216952 (_68278 : real) (_68279 : real) (h1 : term132) : term138 _68278 _68279.
Proof. exact (EQ_MP (@lem5216951 _68278 _68279) (@lem5216127 _68279 _68278 h1)). Qed.
Lemma lem5216954 (b : Prop) (a : Prop) : (a \/ b) = (term400 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5216957 (_68279 : real) (_68278 : real) : (term138 _68278 _68279) = (term424 _68279 _68278).
Proof. exact (@lem5216954 (real_le _68278 _68279) (real_le _68279 _68278)). Qed.
Lemma lem5216960 (_68279 : real) (_68278 : real) (h1 : term132) : term424 _68279 _68278.
Proof. exact (EQ_MP (@lem5216957 _68279 _68278) (@lem5216952 _68278 _68279 h1)). Qed.
Lemma lem5216961 (x' : real -> real) (x : real) (h1 : term132) : term425 x' x.
Proof. exact (@lem5216960 (x' x) (x' x) h1). Qed.
Lemma lem5216964 (x' : real -> real) (x : real) (h1 : term132) (h2 : term420 x' x) : term422 x' x.
Proof. exact (@lem5216961 x' x h1 (@lem5216925 x' x h2)). Qed.
Lemma lem5216965 (x' : real -> real) (x : real) (h1 : term132) : term425 x' x.
Proof. exact (fun h0 : term420 x' x => @lem5216964 x' x h1 h0). Qed.
Lemma lem5216967 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5216968 (x' : real -> real) (x : real) : (term425 x' x) = (term422 x' x).
Proof. exact (@lem5216967 (term422 x' x)). Qed.
Lemma lem5216969 (x' : real -> real) (x : real) (h1 : term132) : term422 x' x.
Proof. exact (EQ_MP (@lem5216968 x' x) (@lem5216965 x' x h1)). Qed.
Lemma lem5216971 (b : Prop) (a : Prop) : (a \/ b) = (term400 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5216972 (_68303 : real) (_68301 : real) (_68300 : real) (_68302 : real) : (term385 _68302 _68303 _68300 _68301) = (term485 _68303 _68301 _68300 _68302).
Proof. exact (@lem5216971 (term383 _68302 _68303 _68300 _68301) (term356 _68300 _68302)). Qed.
Lemma lem5216974 (a : Prop) (b : Prop) : (term402 a b) = (term403 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5216975 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : (term486 _68302 _68303 _68300 _68301) = (term487 _68302 _68303 _68300 _68301).
Proof. exact (@lem5216974 (term356 _68301 _68303) (term380 _68302 _68303 _68300 _68301)). Qed.
Lemma lem5216977 (a : Prop) : (term406 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5216978 (_68301 : real) (_68303 : real) : (term407 _68301 _68303) = (_68301 = _68303).
Proof. exact (@lem5216977 (_68301 = _68303)). Qed.
Lemma lem5216979 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5216980 (_68301 : real) (_68303 : real) : (term408 _68301 _68303) = (term409 _68301 _68303).
Proof. exact (MK_COMB (@lem5216979) (@lem5216978 _68301 _68303)). Qed.
Lemma lem5216982 (a : Prop) (b : Prop) : (term402 a b) = (term403 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5216983 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : (term488 _68302 _68303 _68300 _68301) = (term489 _68302 _68303 _68300 _68301).
Proof. exact (@lem5216982 (real_le _68302 _68303) (term375 _68300 _68301)). Qed.
Lemma lem5216985 (a : Prop) : (term406 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5216986 (_68300 : real) (_68301 : real) : (term439 _68300 _68301) = (real_le _68300 _68301).
Proof. exact (@lem5216985 (real_le _68300 _68301)). Qed.
Lemma lem5216987 (_68302 : real) (_68303 : real) : (term490 _68302 _68303) = (term490 _68302 _68303).
Proof. exact (eq_refl (term490 _68302 _68303)). Qed.
Lemma lem5216988 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : (term489 _68302 _68303 _68300 _68301) = (term491 _68302 _68303 _68300 _68301).
Proof. exact (MK_COMB (@lem5216987 _68302 _68303) (@lem5216986 _68300 _68301)). Qed.
Lemma lem5216989 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : (term488 _68302 _68303 _68300 _68301) = (term491 _68302 _68303 _68300 _68301).
Proof. exact (TRANS (@lem5216983 _68302 _68303 _68300 _68301) (@lem5216988 _68302 _68303 _68300 _68301)). Qed.
Lemma lem5216990 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : (term487 _68302 _68303 _68300 _68301) = (term492 _68302 _68303 _68300 _68301).
Proof. exact (MK_COMB (@lem5216980 _68301 _68303) (@lem5216989 _68302 _68303 _68300 _68301)). Qed.
Lemma lem5216991 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : (term486 _68302 _68303 _68300 _68301) = (term492 _68302 _68303 _68300 _68301).
Proof. exact (TRANS (@lem5216975 _68302 _68303 _68300 _68301) (@lem5216990 _68302 _68303 _68300 _68301)). Qed.
Lemma lem5216992 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5216993 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : (term493 _68302 _68303 _68300 _68301) = (term494 _68302 _68303 _68300 _68301).
Proof. exact (MK_COMB (@lem5216992) (@lem5216991 _68302 _68303 _68300 _68301)). Qed.
Lemma lem5216994 (_68300 : real) (_68302 : real) : (term356 _68300 _68302) = (term356 _68300 _68302).
Proof. exact (eq_refl (term356 _68300 _68302)). Qed.
Lemma lem5216995 (_68303 : real) (_68301 : real) (_68300 : real) (_68302 : real) : (term485 _68303 _68301 _68300 _68302) = (term495 _68303 _68301 _68300 _68302).
Proof. exact (MK_COMB (@lem5216993 _68302 _68303 _68300 _68301) (@lem5216994 _68300 _68302)). Qed.
Lemma lem5216996 (_68303 : real) (_68301 : real) (_68300 : real) (_68302 : real) : (term385 _68302 _68303 _68300 _68301) = (term495 _68303 _68301 _68300 _68302).
Proof. exact (TRANS (@lem5216972 _68303 _68301 _68300 _68302) (@lem5216995 _68303 _68301 _68300 _68302)). Qed.
Lemma lem5216998 (x' : real -> real) (x : real) (h1 : term132) (h2 : term353 x' x) : term496 x' x.
Proof. exact (conj (@lem5216917 x' x h2) (@lem5216969 x' x h1)). Qed.
Lemma lem5216999 (x' : real -> real) (x : real) (h1 : term132) (h2 : term353 x' x) : term497 x' x.
Proof. exact (conj (@lem5216909 x' x) (@lem5216998 x' x h1 h2)). Qed.
Lemma lem5217001 (_68303 : real) (_68301 : real) (_68300 : real) (_68302 : real) : term495 _68303 _68301 _68300 _68302.
Proof. exact (EQ_MP (@lem5216996 _68303 _68301 _68300 _68302) (@lem5216667 _68302 _68303 _68300 _68301)). Qed.
Lemma lem5217002 (x' : real -> real) (x : real) : term498 x' x.
Proof. exact (@lem5217001 (x' x) (x' x) (x' x) x). Qed.
Lemma lem5217005 (x' : real -> real) (x : real) (h1 : term132) (h2 : term353 x' x) : term417 x' x.
Proof. exact (@lem5217002 x' x (@lem5216999 x' x h1 h2)). Qed.
Lemma lem5217006 (x' : real -> real) (x : real) (h1 : term132) (h2 : term353 x' x) : term499 x' x.
Proof. exact (fun h0 : (x' x) = x => @lem5217005 x' x h1 h2). Qed.
Lemma lem5217008 (p : Prop) : (term392 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5217009 (x' : real -> real) (x : real) : (term499 x' x) = (term417 x' x).
Proof. exact (@lem5217008 ((x' x) = x)). Qed.
Lemma lem5217010 (x' : real -> real) (x : real) (h1 : term132) (h2 : term353 x' x) : term417 x' x.
Proof. exact (EQ_MP (@lem5217009 x' x) (@lem5217006 x' x h1 h2)). Qed.
Lemma lem5217016 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5217017 (x : real) (x' : real -> real) (_68280 : real) (s : real -> Prop) : (term373 x x' _68280 s) = (term393 x x' _68280 s).
Proof. exact (@lem5217016 ((x' _68280) = x) (term356 _68280 x) (term391 x' _68280 s)). Qed.
Lemma lem5217033 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5217034 (x' : real -> real) (s : real -> Prop) (_68280 : real) (x : real) : (term394 x x' _68280 s) = (term395 x' s _68280 x).
Proof. exact (@lem5217033 (term391 x' _68280 s) (term356 _68280 x)). Qed.
Lemma lem5217042 (x' : real -> real) (_68280 : real) (x : real) : (term396 x' _68280 x) = (term396 x' _68280 x).
Proof. exact (eq_refl (term396 x' _68280 x)). Qed.
Lemma lem5217043 (x' : real -> real) (s : real -> Prop) (_68280 : real) (x : real) : (term393 x x' _68280 s) = (term397 x' s _68280 x).
Proof. exact (MK_COMB (@lem5217042 x' _68280 x) (@lem5217034 x' s _68280 x)). Qed.
Lemma lem5217054 (x' : real -> real) (s : real -> Prop) (_68280 : real) (x : real) : (term373 x x' _68280 s) = (term397 x' s _68280 x).
Proof. exact (TRANS (@lem5217017 x x' _68280 s) (@lem5217043 x' s _68280 x)). Qed.
Lemma lem5217055 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5217056 (x' : real -> real) (s : real -> Prop) (_68280 : real) (x : real) : (term398 x x' _68280 s) = (term399 x' s _68280 x).
Proof. exact (MK_COMB (@lem5217055) (@lem5217054 x' s _68280 x)). Qed.
Lemma lem5217070 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5217071 (x' : real -> real) (_68280 : real) (x : real) : (term500 x' _68280 x) = (term501 x' _68280 x).
Proof. exact (@lem5217070 ((x' _68280) = x) (term356 _68280 x)). Qed.
Lemma lem5217081 (x' : real -> real) (_68280 : real) (s : real -> Prop) : (term502 x' _68280 s) = (term502 x' _68280 s).
Proof. exact (eq_refl (term502 x' _68280 s)). Qed.
Lemma lem5217082 (s : real -> Prop) (x' : real -> real) (_68280 : real) (x : real) : (term503 s x' _68280 x) = (term504 s x' _68280 x).
Proof. exact (MK_COMB (@lem5217081 x' _68280 s) (@lem5217071 x' _68280 x)). Qed.
Lemma lem5217086 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5217087 (x' : real -> real) (s : real -> Prop) (_68280 : real) (x : real) : (term504 s x' _68280 x) = (term397 x' s _68280 x).
Proof. exact (@lem5217086 ((x' _68280) = x) (term391 x' _68280 s) (term356 _68280 x)). Qed.
Lemma lem5217107 (x' : real -> real) (s : real -> Prop) (_68280 : real) (x : real) : (term503 s x' _68280 x) = (term397 x' s _68280 x).
Proof. exact (TRANS (@lem5217082 s x' _68280 x) (@lem5217087 x' s _68280 x)). Qed.
Lemma lem5217108 (x' : real -> real) (s : real -> Prop) (_68280 : real) (x : real) : ((term373 x x' _68280 s) = (term503 s x' _68280 x)) = ((term397 x' s _68280 x) = (term397 x' s _68280 x)).
Proof. exact (MK_COMB (@lem5217056 x' s _68280 x) (@lem5217107 x' s _68280 x)). Qed.
Lemma lem5217110 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5217111 (x : Prop) : (x = x) = True.
Proof. exact (@lem5217110 Prop x). Qed.
Lemma lem5217112 (x' : real -> real) (s : real -> Prop) (_68280 : real) (x : real) : ((term397 x' s _68280 x) = (term397 x' s _68280 x)) = True.
Proof. exact (@lem5217111 (term397 x' s _68280 x)). Qed.
Lemma lem5217113 (s : real -> Prop) (x' : real -> real) (_68280 : real) (x : real) : ((term373 x x' _68280 s) = (term503 s x' _68280 x)) = True.
Proof. exact (TRANS (@lem5217108 x' s _68280 x) (@lem5217112 x' s _68280 x)). Qed.
Lemma lem5217114 (s : real -> Prop) (x' : real -> real) (_68280 : real) (x : real) : True = ((term373 x x' _68280 s) = (term503 s x' _68280 x)).
Proof. exact (SYM (@lem5217113 s x' _68280 x)). Qed.
Lemma lem5217115 (s : real -> Prop) (x' : real -> real) (_68280 : real) (x : real) : (term373 x x' _68280 s) = (term503 s x' _68280 x).
Proof. exact (EQ_MP (@lem5217114 s x' _68280 x) (@lem0)). Qed.
Lemma lem5217116 (_68280 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term503 s x' _68280 x.
Proof. exact (EQ_MP (@lem5217115 s x' _68280 x) (@lem5216161 _68280 b x s x' h1)). Qed.
Lemma lem5217118 (b : Prop) (a : Prop) : (a \/ b) = (term400 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5217119 (x : real) (x' : real -> real) (_68280 : real) (s : real -> Prop) : (term503 s x' _68280 x) = (term505 x x' _68280 s).
Proof. exact (@lem5217118 (term500 x' _68280 x) (term391 x' _68280 s)). Qed.
Lemma lem5217121 (a : Prop) (b : Prop) : (term402 a b) = (term403 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5217122 (x' : real -> real) (_68280 : real) (x : real) : (term506 x' _68280 x) = (term507 x' _68280 x).
Proof. exact (@lem5217121 (term356 _68280 x) ((x' _68280) = x)). Qed.
Lemma lem5217124 (a : Prop) : (term406 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5217125 (_68280 : real) (x : real) : (term407 _68280 x) = (_68280 = x).
Proof. exact (@lem5217124 (_68280 = x)). Qed.
Lemma lem5217126 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5217127 (_68280 : real) (x : real) : (term408 _68280 x) = (term409 _68280 x).
Proof. exact (MK_COMB (@lem5217126) (@lem5217125 _68280 x)). Qed.
Lemma lem5217128 (x' : real -> real) (_68280 : real) (x : real) : (term484 x' _68280 x) = (term484 x' _68280 x).
Proof. exact (eq_refl (term484 x' _68280 x)). Qed.
Lemma lem5217129 (x' : real -> real) (_68280 : real) (x : real) : (term507 x' _68280 x) = (term508 x' _68280 x).
Proof. exact (MK_COMB (@lem5217127 _68280 x) (@lem5217128 x' _68280 x)). Qed.
Lemma lem5217130 (x' : real -> real) (_68280 : real) (x : real) : (term506 x' _68280 x) = (term508 x' _68280 x).
Proof. exact (TRANS (@lem5217122 x' _68280 x) (@lem5217129 x' _68280 x)). Qed.
Lemma lem5217131 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5217132 (x' : real -> real) (_68280 : real) (x : real) : (term509 x' _68280 x) = (term510 x' _68280 x).
Proof. exact (MK_COMB (@lem5217131) (@lem5217130 x' _68280 x)). Qed.
Lemma lem5217133 (x' : real -> real) (_68280 : real) (s : real -> Prop) : (term391 x' _68280 s) = (term391 x' _68280 s).
Proof. exact (eq_refl (term391 x' _68280 s)). Qed.
Lemma lem5217134 (x : real) (x' : real -> real) (_68280 : real) (s : real -> Prop) : (term505 x x' _68280 s) = (term511 x x' _68280 s).
Proof. exact (MK_COMB (@lem5217132 x' _68280 x) (@lem5217133 x' _68280 s)). Qed.
Lemma lem5217135 (x : real) (x' : real -> real) (_68280 : real) (s : real -> Prop) : (term503 s x' _68280 x) = (term511 x x' _68280 s).
Proof. exact (TRANS (@lem5217119 x x' _68280 s) (@lem5217134 x x' _68280 s)). Qed.
Lemma lem5217137 (x' : real -> real) (x : real) (h1 : term132) (h2 : term353 x' x) : term512 x' x.
Proof. exact (conj (@lem5216901 x) (@lem5217010 x' x h1 h2)). Qed.
Lemma lem5217139 (_68280 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term511 x x' _68280 s.
Proof. exact (EQ_MP (@lem5217135 x x' _68280 s) (@lem5217116 _68280 b x s x' h1)). Qed.
Lemma lem5217140 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term513 x' x s.
Proof. exact (@lem5217139 x b x s x' h1). Qed.
Lemma lem5217143 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term353 x' x) (h3 : term328 b x s x') : term391 x' x s.
Proof. exact (@lem5217140 b x s x' h3 (@lem5217137 x' x h1 h2)). Qed.
Lemma lem5217144 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term353 x' x) (h3 : term328 b x s x') : term514 x' x s.
Proof. exact (fun h0 : term389 x' x s => @lem5217143 b x s x' h1 h2 h3). Qed.
Lemma lem5217146 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5217147 (x' : real -> real) (x : real) (s : real -> Prop) : (term514 x' x s) = (term391 x' x s).
Proof. exact (@lem5217146 (term391 x' x s)). Qed.
Lemma lem5217148 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term353 x' x) (h3 : term328 b x s x') : term391 x' x s.
Proof. exact (EQ_MP (@lem5217147 x' x s) (@lem5217144 b x s x' h1 h2 h3)). Qed.
Lemma lem5217154 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5217155 (b : real) (_68281 : real) (s : real -> Prop) : (term166 s b _68281) = (term515 b _68281 s).
Proof. exact (@lem5217154 (real_le b _68281) (term162 _68281 s)). Qed.
Lemma lem5217161 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5217162 (b : real) (_68281 : real) (s : real -> Prop) : (term516 s b _68281) = (term517 b _68281 s).
Proof. exact (MK_COMB (@lem5217161) (@lem5217155 b _68281 s)). Qed.
Lemma lem5217168 (b : real) (_68281 : real) (s : real -> Prop) : (term515 b _68281 s) = (term515 b _68281 s).
Proof. exact (eq_refl (term515 b _68281 s)). Qed.
Lemma lem5217169 (b : real) (_68281 : real) (s : real -> Prop) : ((term166 s b _68281) = (term515 b _68281 s)) = ((term515 b _68281 s) = (term515 b _68281 s)).
Proof. exact (MK_COMB (@lem5217162 b _68281 s) (@lem5217168 b _68281 s)). Qed.
Lemma lem5217171 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5217172 (x : Prop) : (x = x) = True.
Proof. exact (@lem5217171 Prop x). Qed.
Lemma lem5217173 (b : real) (_68281 : real) (s : real -> Prop) : ((term515 b _68281 s) = (term515 b _68281 s)) = True.
Proof. exact (@lem5217172 (term515 b _68281 s)). Qed.
Lemma lem5217174 (b : real) (_68281 : real) (s : real -> Prop) : ((term166 s b _68281) = (term515 b _68281 s)) = True.
Proof. exact (TRANS (@lem5217169 b _68281 s) (@lem5217173 b _68281 s)). Qed.
Lemma lem5217175 (b : real) (_68281 : real) (s : real -> Prop) : True = ((term166 s b _68281) = (term515 b _68281 s)).
Proof. exact (SYM (@lem5217174 b _68281 s)). Qed.
Lemma lem5217176 (b : real) (_68281 : real) (s : real -> Prop) : (term166 s b _68281) = (term515 b _68281 s).
Proof. exact (EQ_MP (@lem5217175 b _68281 s) (@lem0)). Qed.
Lemma lem5217177 (_68281 : real) (s : real -> Prop) (b : real) (h1 : term169 s b) : term515 b _68281 s.
Proof. exact (EQ_MP (@lem5217176 b _68281 s) (@lem5216139 _68281 s b h1)). Qed.
Lemma lem5217179 (b : Prop) (a : Prop) : (a \/ b) = (term400 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5217180 (s : real -> Prop) (b : real) (_68281 : real) : (term515 b _68281 s) = (term518 s b _68281).
Proof. exact (@lem5217179 (term162 _68281 s) (real_le b _68281)). Qed.
Lemma lem5217182 (a : Prop) : (term406 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5217183 (_68281 : real) (s : real -> Prop) : (term462 _68281 s) = (@IN real _68281 s).
Proof. exact (@lem5217182 (@IN real _68281 s)). Qed.
Lemma lem5217184 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5217185 (_68281 : real) (s : real -> Prop) : (term463 _68281 s) = (term464 _68281 s).
Proof. exact (MK_COMB (@lem5217184) (@lem5217183 _68281 s)). Qed.
Lemma lem5217186 (b : real) (_68281 : real) : (real_le b _68281) = (real_le b _68281).
Proof. exact (eq_refl (real_le b _68281)). Qed.
Lemma lem5217187 (s : real -> Prop) (b : real) (_68281 : real) : (term518 s b _68281) = (term149 s b _68281).
Proof. exact (MK_COMB (@lem5217185 _68281 s) (@lem5217186 b _68281)). Qed.
Lemma lem5217188 (s : real -> Prop) (b : real) (_68281 : real) : (term515 b _68281 s) = (term149 s b _68281).
Proof. exact (TRANS (@lem5217180 s b _68281) (@lem5217187 s b _68281)). Qed.
Lemma lem5217191 (_68281 : real) (s : real -> Prop) (b : real) (h1 : term169 s b) : term149 s b _68281.
Proof. exact (EQ_MP (@lem5217188 s b _68281) (@lem5217177 _68281 s b h1)). Qed.
Lemma lem5217192 (x' : real -> real) (x : real) (s : real -> Prop) (b : real) (h1 : term169 s b) : term519 s b x' x.
Proof. exact (@lem5217191 (x' x) s b h1). Qed.
Lemma lem5217195 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term132) (h2 : term353 x' x) (h3 : term328 b x s x') (h4 : term169 s b) : term520 b x' x.
Proof. exact (@lem5217192 x' x s b h4 (@lem5217148 b x s x' h1 h2 h3)). Qed.
Lemma lem5217196 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term132) (h2 : term353 x' x) (h3 : term328 b x s x') (h4 : term169 s b) : term521 b x' x.
Proof. exact (fun h0 : term522 b x' x => @lem5217195 x x' s b h1 h2 h3 h4). Qed.
Lemma lem5217198 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5217199 (b : real) (x' : real -> real) (x : real) : (term521 b x' x) = (term520 b x' x).
Proof. exact (@lem5217198 (term520 b x' x)). Qed.
Lemma lem5217200 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term132) (h2 : term353 x' x) (h3 : term328 b x s x') (h4 : term169 s b) : term520 b x' x.
Proof. exact (EQ_MP (@lem5217199 b x' x) (@lem5217196 x x' s b h1 h2 h3 h4)). Qed.
Lemma lem5217202 (s : real -> Prop) (b : real) (h1 : term169 s b) : @IN real b s.
Proof. exact (proj1 (@lem5215785 s b h1)). Qed.
Lemma lem5217203 (s : real -> Prop) (b : real) (h1 : term169 s b) : term458 b s.
Proof. exact (fun h0 : term162 b s => @lem5217202 s b h1). Qed.
Lemma lem5217205 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5217206 (b : real) (s : real -> Prop) : (term458 b s) = (@IN real b s).
Proof. exact (@lem5217205 (@IN real b s)). Qed.
Lemma lem5217207 (s : real -> Prop) (b : real) (h1 : term169 s b) : @IN real b s.
Proof. exact (EQ_MP (@lem5217206 b s) (@lem5217203 s b h1)). Qed.
Lemma lem5217209 (_68280 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term465 s x' _68280.
Proof. exact (EQ_MP (@lem5216738 s x' _68280) (@lem5216727 _68280 b x s x' h1)). Qed.
Lemma lem5217210 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term465 s x' b.
Proof. exact (@lem5217209 b b x s x' h1). Qed.
Lemma lem5217213 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term353 x' b.
Proof. exact (@lem5217210 b x s x' h1 (@lem5217207 s b h2)). Qed.
Lemma lem5217214 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term466 x' b.
Proof. exact (fun h0 : term448 x' b => @lem5217213 x x' s b h1 h2). Qed.
Lemma lem5217216 (p : Prop) : (term392 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5217217 (x' : real -> real) (b : real) : (term466 x' b) = (term353 x' b).
Proof. exact (@lem5217216 (term448 x' b)). Qed.
Lemma lem5217218 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term353 x' b.
Proof. exact (EQ_MP (@lem5217217 x' b) (@lem5217214 x x' s b h1 h2)). Qed.
Lemma lem5217234 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5217235 (_68275 : real) (_68276 : real) (_68277 : real) : (term523 _68276 _68275 _68277) = (term524 _68275 _68276 _68277).
Proof. exact (@lem5217234 (real_le _68275 _68277) (term375 _68276 _68277)). Qed.
Lemma lem5217241 (_68275 : real) (_68276 : real) : (term525 _68275 _68276) = (term525 _68275 _68276).
Proof. exact (eq_refl (term525 _68275 _68276)). Qed.
Lemma lem5217242 (_68275 : real) (_68276 : real) (_68277 : real) : (term374 _68276 _68275 _68277) = (term526 _68275 _68276 _68277).
Proof. exact (MK_COMB (@lem5217241 _68275 _68276) (@lem5217235 _68275 _68276 _68277)). Qed.
Lemma lem5217246 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5217247 (_68275 : real) (_68276 : real) (_68277 : real) : (term526 _68275 _68276 _68277) = (term527 _68275 _68276 _68277).
Proof. exact (@lem5217246 (real_le _68275 _68277) (term375 _68275 _68276) (term375 _68276 _68277)). Qed.
Lemma lem5217263 (_68275 : real) (_68276 : real) (_68277 : real) : (term374 _68276 _68275 _68277) = (term527 _68275 _68276 _68277).
Proof. exact (TRANS (@lem5217242 _68275 _68276 _68277) (@lem5217247 _68275 _68276 _68277)). Qed.
Lemma lem5217264 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5217265 (_68275 : real) (_68276 : real) (_68277 : real) : (term528 _68276 _68275 _68277) = (term529 _68275 _68276 _68277).
Proof. exact (MK_COMB (@lem5217264) (@lem5217263 _68275 _68276 _68277)). Qed.
Lemma lem5217269 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5217270 (_68276 : real) (_68275 : real) (_68277 : real) : (term530 _68276 _68275 _68277) = (term374 _68276 _68275 _68277).
Proof. exact (@lem5217269 (term375 _68275 _68276) (term375 _68276 _68277) (real_le _68275 _68277)). Qed.
Lemma lem5217284 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5217285 (_68275 : real) (_68276 : real) (_68277 : real) : (term523 _68276 _68275 _68277) = (term524 _68275 _68276 _68277).
Proof. exact (@lem5217284 (real_le _68275 _68277) (term375 _68276 _68277)). Qed.
Lemma lem5217291 (_68275 : real) (_68276 : real) : (term525 _68275 _68276) = (term525 _68275 _68276).
Proof. exact (eq_refl (term525 _68275 _68276)). Qed.
Lemma lem5217292 (_68275 : real) (_68276 : real) (_68277 : real) : (term374 _68276 _68275 _68277) = (term526 _68275 _68276 _68277).
Proof. exact (MK_COMB (@lem5217291 _68275 _68276) (@lem5217285 _68275 _68276 _68277)). Qed.
Lemma lem5217296 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5217297 (_68275 : real) (_68276 : real) (_68277 : real) : (term526 _68275 _68276 _68277) = (term527 _68275 _68276 _68277).
Proof. exact (@lem5217296 (real_le _68275 _68277) (term375 _68275 _68276) (term375 _68276 _68277)). Qed.
Lemma lem5217313 (_68275 : real) (_68276 : real) (_68277 : real) : (term374 _68276 _68275 _68277) = (term527 _68275 _68276 _68277).
Proof. exact (TRANS (@lem5217292 _68275 _68276 _68277) (@lem5217297 _68275 _68276 _68277)). Qed.
Lemma lem5217314 (_68275 : real) (_68276 : real) (_68277 : real) : (term530 _68276 _68275 _68277) = (term527 _68275 _68276 _68277).
Proof. exact (TRANS (@lem5217270 _68276 _68275 _68277) (@lem5217313 _68275 _68276 _68277)). Qed.
Lemma lem5217315 (_68275 : real) (_68276 : real) (_68277 : real) : ((term374 _68276 _68275 _68277) = (term530 _68276 _68275 _68277)) = ((term527 _68275 _68276 _68277) = (term527 _68275 _68276 _68277)).
Proof. exact (MK_COMB (@lem5217265 _68275 _68276 _68277) (@lem5217314 _68275 _68276 _68277)). Qed.
Lemma lem5217317 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5217318 (x : Prop) : (x = x) = True.
Proof. exact (@lem5217317 Prop x). Qed.
Lemma lem5217319 (_68275 : real) (_68276 : real) (_68277 : real) : ((term527 _68275 _68276 _68277) = (term527 _68275 _68276 _68277)) = True.
Proof. exact (@lem5217318 (term527 _68275 _68276 _68277)). Qed.
Lemma lem5217320 (_68276 : real) (_68275 : real) (_68277 : real) : ((term374 _68276 _68275 _68277) = (term530 _68276 _68275 _68277)) = True.
Proof. exact (TRANS (@lem5217315 _68275 _68276 _68277) (@lem5217319 _68275 _68276 _68277)). Qed.
Lemma lem5217321 (_68276 : real) (_68275 : real) (_68277 : real) : True = ((term374 _68276 _68275 _68277) = (term530 _68276 _68275 _68277)).
Proof. exact (SYM (@lem5217320 _68276 _68275 _68277)). Qed.
Lemma lem5217322 (_68276 : real) (_68275 : real) (_68277 : real) : (term374 _68276 _68275 _68277) = (term530 _68276 _68275 _68277).
Proof. exact (EQ_MP (@lem5217321 _68276 _68275 _68277) (@lem0)). Qed.
Lemma lem5217323 (_68276 : real) (_68275 : real) (_68277 : real) (h1 : term148) : term530 _68276 _68275 _68277.
Proof. exact (EQ_MP (@lem5217322 _68276 _68275 _68277) (@lem5216121 _68276 _68275 _68277 h1)). Qed.
Lemma lem5217325 (b : Prop) (a : Prop) : (a \/ b) = (term400 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5217326 (_68275 : real) (_68276 : real) (_68277 : real) : (term530 _68276 _68275 _68277) = (term531 _68275 _68276 _68277).
Proof. exact (@lem5217325 (term532 _68276 _68275 _68277) (term375 _68276 _68277)). Qed.
Lemma lem5217328 (a : Prop) (b : Prop) : (term402 a b) = (term403 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5217329 (_68276 : real) (_68275 : real) (_68277 : real) : (term533 _68276 _68275 _68277) = (term534 _68276 _68275 _68277).
Proof. exact (@lem5217328 (term375 _68275 _68276) (real_le _68275 _68277)). Qed.
Lemma lem5217331 (a : Prop) : (term406 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5217332 (_68275 : real) (_68276 : real) : (term439 _68275 _68276) = (real_le _68275 _68276).
Proof. exact (@lem5217331 (real_le _68275 _68276)). Qed.
Lemma lem5217333 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5217334 (_68275 : real) (_68276 : real) : (term535 _68275 _68276) = (term536 _68275 _68276).
Proof. exact (MK_COMB (@lem5217333) (@lem5217332 _68275 _68276)). Qed.
Lemma lem5217335 (_68275 : real) (_68277 : real) : (term375 _68275 _68277) = (term375 _68275 _68277).
Proof. exact (eq_refl (term375 _68275 _68277)). Qed.
Lemma lem5217336 (_68276 : real) (_68275 : real) (_68277 : real) : (term534 _68276 _68275 _68277) = (term537 _68276 _68275 _68277).
Proof. exact (MK_COMB (@lem5217334 _68275 _68276) (@lem5217335 _68275 _68277)). Qed.
Lemma lem5217337 (_68276 : real) (_68275 : real) (_68277 : real) : (term533 _68276 _68275 _68277) = (term537 _68276 _68275 _68277).
Proof. exact (TRANS (@lem5217329 _68276 _68275 _68277) (@lem5217336 _68276 _68275 _68277)). Qed.
Lemma lem5217338 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5217339 (_68276 : real) (_68275 : real) (_68277 : real) : (term538 _68276 _68275 _68277) = (term539 _68276 _68275 _68277).
Proof. exact (MK_COMB (@lem5217338) (@lem5217337 _68276 _68275 _68277)). Qed.
Lemma lem5217340 (_68276 : real) (_68277 : real) : (term375 _68276 _68277) = (term375 _68276 _68277).
Proof. exact (eq_refl (term375 _68276 _68277)). Qed.
Lemma lem5217341 (_68275 : real) (_68276 : real) (_68277 : real) : (term531 _68275 _68276 _68277) = (term540 _68275 _68276 _68277).
Proof. exact (MK_COMB (@lem5217339 _68276 _68275 _68277) (@lem5217340 _68276 _68277)). Qed.
Lemma lem5217342 (_68275 : real) (_68276 : real) (_68277 : real) : (term530 _68276 _68275 _68277) = (term540 _68275 _68276 _68277).
Proof. exact (TRANS (@lem5217326 _68275 _68276 _68277) (@lem5217341 _68275 _68276 _68277)). Qed.
Lemma lem5217344 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term132) (h2 : term353 x' x) (h3 : term328 b x s x') (h4 : term169 s b) : term541 x x' b.
Proof. exact (conj (@lem5217200 x x' s b h1 h2 h3 h4) (@lem5217218 x x' s b h3 h4)). Qed.
Lemma lem5217346 (_68275 : real) (_68276 : real) (_68277 : real) (h1 : term148) : term540 _68275 _68276 _68277.
Proof. exact (EQ_MP (@lem5217342 _68275 _68276 _68277) (@lem5217323 _68276 _68275 _68277 h1)). Qed.
Lemma lem5217347 (x : real) (x' : real -> real) (b : real) (h1 : term148) : term542 x x' b.
Proof. exact (@lem5217346 b (x' x) (x' b) h1). Qed.
Lemma lem5217350 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term353 x' x) (h4 : term328 b x s x') (h5 : term169 s b) : term543 x x' b.
Proof. exact (@lem5217347 x x' b h1 (@lem5217344 x x' s b h2 h3 h4 h5)). Qed.
Lemma lem5217351 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term353 x' x) (h4 : term328 b x s x') (h5 : term169 s b) : term544 x x' b.
Proof. exact (fun h0 : term545 x x' b => @lem5217350 x x' s b h1 h2 h3 h4 h5). Qed.
Lemma lem5217353 (p : Prop) : (term392 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5217354 (x : real) (x' : real -> real) (b : real) : (term544 x x' b) = (term543 x x' b).
Proof. exact (@lem5217353 (term545 x x' b)). Qed.
Lemma lem5217355 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term353 x' x) (h4 : term328 b x s x') (h5 : term169 s b) : term543 x x' b.
Proof. exact (EQ_MP (@lem5217354 x x' b) (@lem5217351 x x' s b h1 h2 h3 h4 h5)). Qed.
Lemma lem5217357 (_68279 : real) (_68278 : real) (h1 : term132) : term424 _68279 _68278.
Proof. exact (EQ_MP (@lem5216957 _68279 _68278) (@lem5216952 _68278 _68279 h1)). Qed.
Lemma lem5217358 (b : real) (x' : real -> real) (x : real) (h1 : term132) : term546 b x' x.
Proof. exact (@lem5217357 (x' b) (x' x) h1). Qed.
Lemma lem5217361 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term353 x' x) (h4 : term328 b x s x') (h5 : term169 s b) : term545 b x' x.
Proof. exact (@lem5217358 b x' x h2 (@lem5217355 x x' s b h1 h2 h3 h4 h5)). Qed.
Lemma lem5217362 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term353 x' x) (h4 : term328 b x s x') (h5 : term169 s b) : term547 b x' x.
Proof. exact (fun h0 : term543 b x' x => @lem5217361 x x' s b h1 h2 h3 h4 h5). Qed.
Lemma lem5217364 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5217365 (b : real) (x' : real -> real) (x : real) : (term547 b x' x) = (term545 b x' x).
Proof. exact (@lem5217364 (term545 b x' x)). Qed.
Lemma lem5217366 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term353 x' x) (h4 : term328 b x s x') (h5 : term169 s b) : term545 b x' x.
Proof. exact (EQ_MP (@lem5217365 b x' x) (@lem5217362 x x' s b h1 h2 h3 h4 h5)). Qed.
Lemma lem5217384 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5217385 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : (term383 _68302 _68303 _68300 _68301) = (term426 _68302 _68303 _68300 _68301).
Proof. exact (@lem5217384 (real_le _68302 _68303) (term356 _68301 _68303) (term375 _68300 _68301)). Qed.
Lemma lem5217403 (_68300 : real) (_68302 : real) : (term427 _68300 _68302) = (term427 _68300 _68302).
Proof. exact (eq_refl (term427 _68300 _68302)). Qed.
Lemma lem5217404 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : (term385 _68302 _68303 _68300 _68301) = (term428 _68302 _68303 _68300 _68301).
Proof. exact (MK_COMB (@lem5217403 _68300 _68302) (@lem5217385 _68302 _68303 _68300 _68301)). Qed.
Lemma lem5217408 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5217409 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : (term428 _68302 _68303 _68300 _68301) = (term429 _68302 _68303 _68300 _68301).
Proof. exact (@lem5217408 (real_le _68302 _68303) (term356 _68300 _68302) (term430 _68303 _68300 _68301)). Qed.
Lemma lem5217439 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : (term385 _68302 _68303 _68300 _68301) = (term429 _68302 _68303 _68300 _68301).
Proof. exact (TRANS (@lem5217404 _68302 _68303 _68300 _68301) (@lem5217409 _68302 _68303 _68300 _68301)). Qed.
Lemma lem5217440 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5217441 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : (term431 _68302 _68303 _68300 _68301) = (term432 _68302 _68303 _68300 _68301).
Proof. exact (MK_COMB (@lem5217440) (@lem5217439 _68302 _68303 _68300 _68301)). Qed.
Lemma lem5217471 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : (term429 _68302 _68303 _68300 _68301) = (term429 _68302 _68303 _68300 _68301).
Proof. exact (eq_refl (term429 _68302 _68303 _68300 _68301)). Qed.
Lemma lem5217472 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : ((term385 _68302 _68303 _68300 _68301) = (term429 _68302 _68303 _68300 _68301)) = ((term429 _68302 _68303 _68300 _68301) = (term429 _68302 _68303 _68300 _68301)).
Proof. exact (MK_COMB (@lem5217441 _68302 _68303 _68300 _68301) (@lem5217471 _68302 _68303 _68300 _68301)). Qed.
Lemma lem5217474 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5217475 (x : Prop) : (x = x) = True.
Proof. exact (@lem5217474 Prop x). Qed.
Lemma lem5217476 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : ((term429 _68302 _68303 _68300 _68301) = (term429 _68302 _68303 _68300 _68301)) = True.
Proof. exact (@lem5217475 (term429 _68302 _68303 _68300 _68301)). Qed.
Lemma lem5217477 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : ((term385 _68302 _68303 _68300 _68301) = (term429 _68302 _68303 _68300 _68301)) = True.
Proof. exact (TRANS (@lem5217472 _68302 _68303 _68300 _68301) (@lem5217476 _68302 _68303 _68300 _68301)). Qed.
Lemma lem5217478 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : True = ((term385 _68302 _68303 _68300 _68301) = (term429 _68302 _68303 _68300 _68301)).
Proof. exact (SYM (@lem5217477 _68302 _68303 _68300 _68301)). Qed.
Lemma lem5217479 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : (term385 _68302 _68303 _68300 _68301) = (term429 _68302 _68303 _68300 _68301).
Proof. exact (EQ_MP (@lem5217478 _68302 _68303 _68300 _68301) (@lem0)). Qed.
Lemma lem5217480 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : term429 _68302 _68303 _68300 _68301.
Proof. exact (EQ_MP (@lem5217479 _68302 _68303 _68300 _68301) (@lem5216667 _68302 _68303 _68300 _68301)). Qed.
Lemma lem5217482 (b : Prop) (a : Prop) : (a \/ b) = (term400 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5217483 (_68300 : real) (_68301 : real) (_68302 : real) (_68303 : real) : (term429 _68302 _68303 _68300 _68301) = (term433 _68300 _68301 _68302 _68303).
Proof. exact (@lem5217482 (term434 _68302 _68303 _68300 _68301) (real_le _68302 _68303)). Qed.
Lemma lem5217485 (a : Prop) (b : Prop) : (term402 a b) = (term403 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5217486 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : (term435 _68302 _68303 _68300 _68301) = (term436 _68302 _68303 _68300 _68301).
Proof. exact (@lem5217485 (term356 _68300 _68302) (term430 _68303 _68300 _68301)). Qed.
Lemma lem5217488 (a : Prop) : (term406 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5217489 (_68300 : real) (_68302 : real) : (term407 _68300 _68302) = (_68300 = _68302).
Proof. exact (@lem5217488 (_68300 = _68302)). Qed.
Lemma lem5217490 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5217491 (_68300 : real) (_68302 : real) : (term408 _68300 _68302) = (term409 _68300 _68302).
Proof. exact (MK_COMB (@lem5217490) (@lem5217489 _68300 _68302)). Qed.
Lemma lem5217493 (a : Prop) (b : Prop) : (term402 a b) = (term403 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5217494 (_68303 : real) (_68300 : real) (_68301 : real) : (term437 _68303 _68300 _68301) = (term438 _68303 _68300 _68301).
Proof. exact (@lem5217493 (term356 _68301 _68303) (term375 _68300 _68301)). Qed.
Lemma lem5217496 (a : Prop) : (term406 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5217497 (_68301 : real) (_68303 : real) : (term407 _68301 _68303) = (_68301 = _68303).
Proof. exact (@lem5217496 (_68301 = _68303)). Qed.
Lemma lem5217498 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5217499 (_68301 : real) (_68303 : real) : (term408 _68301 _68303) = (term409 _68301 _68303).
Proof. exact (MK_COMB (@lem5217498) (@lem5217497 _68301 _68303)). Qed.
Lemma lem5217501 (a : Prop) : (term406 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5217502 (_68300 : real) (_68301 : real) : (term439 _68300 _68301) = (real_le _68300 _68301).
Proof. exact (@lem5217501 (real_le _68300 _68301)). Qed.
Lemma lem5217503 (_68303 : real) (_68300 : real) (_68301 : real) : (term438 _68303 _68300 _68301) = (term440 _68303 _68300 _68301).
Proof. exact (MK_COMB (@lem5217499 _68301 _68303) (@lem5217502 _68300 _68301)). Qed.
Lemma lem5217504 (_68303 : real) (_68300 : real) (_68301 : real) : (term437 _68303 _68300 _68301) = (term440 _68303 _68300 _68301).
Proof. exact (TRANS (@lem5217494 _68303 _68300 _68301) (@lem5217503 _68303 _68300 _68301)). Qed.
Lemma lem5217505 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : (term436 _68302 _68303 _68300 _68301) = (term441 _68302 _68303 _68300 _68301).
Proof. exact (MK_COMB (@lem5217491 _68300 _68302) (@lem5217504 _68303 _68300 _68301)). Qed.
Lemma lem5217506 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : (term435 _68302 _68303 _68300 _68301) = (term441 _68302 _68303 _68300 _68301).
Proof. exact (TRANS (@lem5217486 _68302 _68303 _68300 _68301) (@lem5217505 _68302 _68303 _68300 _68301)). Qed.
Lemma lem5217507 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5217508 (_68302 : real) (_68303 : real) (_68300 : real) (_68301 : real) : (term442 _68302 _68303 _68300 _68301) = (term443 _68302 _68303 _68300 _68301).
Proof. exact (MK_COMB (@lem5217507) (@lem5217506 _68302 _68303 _68300 _68301)). Qed.
Lemma lem5217509 (_68302 : real) (_68303 : real) : (real_le _68302 _68303) = (real_le _68302 _68303).
Proof. exact (eq_refl (real_le _68302 _68303)). Qed.
Lemma lem5217510 (_68300 : real) (_68301 : real) (_68302 : real) (_68303 : real) : (term433 _68300 _68301 _68302 _68303) = (term444 _68300 _68301 _68302 _68303).
Proof. exact (MK_COMB (@lem5217508 _68302 _68303 _68300 _68301) (@lem5217509 _68302 _68303)). Qed.
Lemma lem5217511 (_68300 : real) (_68301 : real) (_68302 : real) (_68303 : real) : (term429 _68302 _68303 _68300 _68301) = (term444 _68300 _68301 _68302 _68303).
Proof. exact (TRANS (@lem5217483 _68300 _68301 _68302 _68303) (@lem5217510 _68300 _68301 _68302 _68303)). Qed.
Lemma lem5217513 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term353 x' x) (h4 : term328 b x s x') (h5 : term169 s b) : term548 b x' x.
Proof. exact (conj (@lem5216894 x' x) (@lem5217366 x x' s b h1 h2 h3 h4 h5)). Qed.
Lemma lem5217514 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term353 x' x) (h4 : term328 b x s x') (h5 : term169 s b) : term549 b x' x.
Proof. exact (conj (@lem5216886 x x' s b h4 h5) (@lem5217513 x x' s b h1 h2 h3 h4 h5)). Qed.
Lemma lem5217516 (_68300 : real) (_68301 : real) (_68302 : real) (_68303 : real) : term444 _68300 _68301 _68302 _68303.
Proof. exact (EQ_MP (@lem5217511 _68300 _68301 _68302 _68303) (@lem5217480 _68302 _68303 _68300 _68301)). Qed.
Lemma lem5217517 (b : real) (x' : real -> real) (x : real) : term550 b x' x.
Proof. exact (@lem5217516 (x' b) (x' x) x (x' x)). Qed.
Lemma lem5217520 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term353 x' x) (h4 : term328 b x s x') (h5 : term169 s b) : term448 x' x.
Proof. exact (@lem5217517 b x' x (@lem5217514 x x' s b h1 h2 h3 h4 h5)). Qed.
Lemma lem5217521 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') (h4 : term169 s b) : term449 x' x.
Proof. exact (fun h0 : term353 x' x => @lem5217520 x x' s b h1 h2 h0 h3 h4). Qed.
Lemma lem5217523 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5217524 (x' : real -> real) (x : real) : (term449 x' x) = (term448 x' x).
Proof. exact (@lem5217523 (term448 x' x)). Qed.
Lemma lem5217525 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') (h4 : term169 s b) : term448 x' x.
Proof. exact (EQ_MP (@lem5217524 x' x) (@lem5217521 x x' s b h1 h2 h3 h4)). Qed.
Lemma lem5217527 (a : Prop) (b : Prop) : (term450 a b) = (term451 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5217528 (x : real) (x' : real -> real) (_68280 : real) : (term372 x x' _68280) = (term452 x x' _68280).
Proof. exact (@lem5217527 (_68280 = x) (term448 x' _68280)). Qed.
Lemma lem5217530 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5217531 (x : real) (x' : real -> real) (_68280 : real) : (term452 x x' _68280) = (term453 x x' _68280).
Proof. exact (@lem5217530 (term454 x x' _68280)). Qed.
Lemma lem5217532 (x : real) (x' : real -> real) (_68280 : real) : (term372 x x' _68280) = (term453 x x' _68280).
Proof. exact (TRANS (@lem5217528 x x' _68280) (@lem5217531 x x' _68280)). Qed.
Lemma lem5217534 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') (h4 : term169 s b) : term455 x' x.
Proof. exact (conj (@lem5216686 x) (@lem5217525 x x' s b h1 h2 h3 h4)). Qed.
Lemma lem5217536 (_68280 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term453 x x' _68280.
Proof. exact (EQ_MP (@lem5217532 x x' _68280) (@lem5216145 _68280 b x s x' h1)). Qed.
Lemma lem5217537 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term456 x' x.
Proof. exact (@lem5217536 x b x s x' h1). Qed.
Lemma lem5217540 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') (h4 : term169 s b) : False.
Proof. exact (@lem5217537 b x s x' h3 (@lem5217534 x x' s b h1 h2 h3 h4)). Qed.
Lemma lem5217541 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') (h4 : term169 s b) : term457.
Proof. exact (fun h0 : ~ False => @lem5217540 x x' s b h1 h2 h3 h4). Qed.
Lemma lem5217543 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5217544 : term457 = False.
Proof. exact (@lem5217543 False). Qed.
Lemma lem5217545 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') (h4 : term169 s b) : False.
Proof. exact (EQ_MP (@lem5217544) (@lem5217541 x x' s b h1 h2 h3 h4)). Qed.
Lemma lem5217546 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') (h4 : term169 s b) : term132 = False.
Proof. exact (prop_ext (fun h5 : term132 => @lem5217545 x x' s b h1 h2 h3 h4) (fun h5 : False => @lem5215929 h2)). Qed.
Lemma lem5217547 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') (h4 : term169 s b) : False.
Proof. exact (EQ_MP (@lem5217546 x x' s b h1 h2 h3 h4) (@lem5215929 h2)). Qed.
Lemma lem5217548 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : (term165 s) = False.
Proof. exact (prop_ext (fun h4 : term165 s => @lem5216617 b x s x' h1 h2 h3) (fun h4 : False => @lem5215888 s h2)). Qed.
Lemma lem5217549 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : False.
Proof. exact (EQ_MP (@lem5217548 b x s x' h1 h2 h3) (@lem5215888 s h2)). Qed.
Lemma lem5217550 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : term132 = False.
Proof. exact (prop_ext (fun h4 : term132 => @lem5217549 b x s x' h1 h2 h3) (fun h4 : False => @lem5215828 h1)). Qed.
Lemma lem5217551 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : False.
Proof. exact (EQ_MP (@lem5217550 b x s x' h1 h2 h3) (@lem5215828 h1)). Qed.
Lemma lem5217552 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') : False.
Proof. exact (or_elim (@lem5215781 b x s x' h3) (fun h0 : term165 s => @lem5217551 b x s x' h2 h0 h3) (fun h0 : term169 s b => @lem5217547 x x' s b h1 h2 h3 h0)). Qed.
Lemma lem5217553 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') : (term328 b x s x') = False.
Proof. exact (prop_ext (fun h4 : term328 b x s x' => @lem5217552 b x s x' h1 h2 h3) (fun h4 : False => @lem5215777 b x s x' h3)). Qed.
Lemma lem5217554 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') : False.
Proof. exact (EQ_MP (@lem5217553 b x s x' h1 h2 h3) (@lem5215777 b x s x' h3)). Qed.
Lemma lem5217555 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') : term132 = False.
Proof. exact (prop_ext (fun h4 : term132 => @lem5217554 b x s x' h1 h2 h3) (fun h4 : False => @lem5215666 h2)). Qed.
Lemma lem5217556 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') : False.
Proof. exact (EQ_MP (@lem5217555 b x s x' h1 h2 h3) (@lem5215666 h2)). Qed.
Lemma lem5217557 (b : real) (x : real) (s : real -> Prop) (h1 : term148) (h2 : term132) (h3 : term331 b x s) : False.
Proof. exact (ex_elim (@lem5215610 b x s h3) (fun x' : real -> real => fun h0 : term330 b x s x' => @lem5217556 b x s x' h1 h2 h0)). Qed.
Lemma lem5217558 (x : real) (s : real -> Prop) (h1 : term148) (h2 : term132) (h3 : term333 x s) : False.
Proof. exact (ex_elim (@lem5215609 x s h3) (fun b : real => fun h0 : term332 x s b => @lem5217557 b x s h1 h2 h0)). Qed.
Lemma lem5217559 (x : real) (h1 : term148) (h2 : term132) (h3 : term335 x) : False.
Proof. exact (ex_elim (@lem5215608 x h3) (fun s : real -> Prop => fun h0 : term334 x s => @lem5217558 x s h1 h2 h0)). Qed.
Lemma lem5217560 (h1 : term148) (h2 : term132) (h3 : term125) : False.
Proof. exact (ex_elim (@lem5215456 h3) (fun x : real => fun h0 : term336 x => @lem5217559 x h1 h2 h0)). Qed.
Lemma lem5217561 (h1 : term148) (h2 : term132) (h3 : term125) : term132 = False.
Proof. exact (prop_ext (fun h4 : term132 => @lem5217560 h1 h2 h3) (fun h4 : False => @lem5215607 h2)). Qed.
Lemma lem5217562 (h1 : term148) (h2 : term132) (h3 : term125) : False.
Proof. exact (EQ_MP (@lem5217561 h1 h2 h3) (@lem5215607 h2)). Qed.
Lemma lem5217563 (h1 : term148) (h2 : term125) : term130.
Proof. exact (fun h0 : term132 => @lem5217562 h1 h0 h2). Qed.
Lemma lem5217564 : term130 = term131.
Proof. exact (@lem69 term132). Qed.
Lemma lem5217565 (h1 : term148) (h2 : term125) : term131.
Proof. exact (EQ_MP (@lem5217564) (@lem5217563 h1 h2)). Qed.
Lemma lem5217566 (h1 : term125) : term135.
Proof. exact (fun h0 : term148 => @lem5217565 h0 h1). Qed.
Lemma lem5217567 : term137.
Proof. exact (fun h0 : term125 => @lem5217566 h0). Qed.
Lemma lem5217568 : term126.
Proof. exact (EQ_MP (@lem5214931) (@lem5217567)). Qed.
Lemma lem5217570 : term126.
Proof. exact (@lem5214497 (@lem5217568)). Qed.
Lemma lem5217571 (h1 : term125) : term134.
Proof. exact (@lem5217570 (@lem5214482 h1)). Qed.
Lemma lem5217572 (h1 : term125) : term130.
Proof. exact (@lem5217571 h1 (@lem1339577)). Qed.
Lemma lem5217573 (h1 : term125) : False.
Proof. exact (@lem5217572 h1 (@lem1339697)). Qed.
Lemma lem5217574 (h1 : term125) : term125 = False.
Proof. exact (prop_ext (fun h2 : term125 => @lem5217573 h1) (fun h2 : False => @lem5214482 h1)). Qed.
Lemma lem5217575 (h1 : term125) : False.
Proof. exact (EQ_MP (@lem5217574 h1) (@lem5214482 h1)). Qed.
Lemma lem5217576 : term124.
Proof. exact (fun h0 : term125 => @lem5217575 h0). Qed.
Lemma lem5217577 : term122.
Proof. exact (EQ_MP (@lem5214481) (@lem5217576)). Qed.
Lemma lem5217578 : term109.
Proof. exact (EQ_MP (@lem5214477) (@lem5217577)). Qed.
Lemma lem5217579 : term72.
Proof. exact (EQ_MP (@lem5214389) (@lem5217578)). Qed.
Lemma lem5217580 : term42.
Proof. exact (@lem5214160 (@lem5217579)). Qed.
Lemma lem5217581 : term41.
Proof. exact (EQ_MP (@lem5214127) (@lem5217580)). Qed.
