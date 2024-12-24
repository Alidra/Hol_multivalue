Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_EQ_RDIV_EQ_term_abbrevs.
Require Import REAL_LE_LDIV_EQ_spec.
Require Import REAL_LE_RDIV_EQ_spec.
Require Import thm0_spec.
Require Import thm1339379_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem1629052 (x : real) : term0 x.
Proof. exact (@lem1628775 x). Qed.
Lemma lem1629053 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1629054 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1629053 x) (@lem1629052 x)). Qed.
Lemma lem1629055 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1629054 x y). Qed.
Lemma lem1629056 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1629057 (x : real) (y : real) : term3 x y.
Proof. exact (EQ_MP (@lem1629056 x y) (@lem1629055 x y)). Qed.
Lemma lem1629058 (x : real) (y : real) (z : real) : term4 x y z.
Proof. exact (@lem1629057 x y z). Qed.
Lemma lem1629059 (x : real) (y : real) (z : real) : (term4 x y z) = (term5 x y z).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem1629060 (x : real) (y : real) (z : real) : term5 x y z.
Proof. exact (EQ_MP (@lem1629059 x y z) (@lem1629058 x y z)). Qed.
Lemma lem1629061 (z : real) (h1 : term6 z) : term6 z.
Proof. exact (h1). Qed.
Lemma lem1629062 (x : real) (y : real) (z : real) (h1 : term6 z) : (term7 x z y) = (term8 x y z).
Proof. exact (@lem1629060 x y z (@lem1629061 z h1)). Qed.
Lemma lem1629068 (x : real) : term9 x.
Proof. exact (@lem1628574 x). Qed.
Lemma lem1629069 (x : real) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1629070 (x : real) : term10 x.
Proof. exact (EQ_MP (@lem1629069 x) (@lem1629068 x)). Qed.
Lemma lem1629071 (x : real) (y : real) : term11 x y.
Proof. exact (@lem1629070 x y). Qed.
Lemma lem1629072 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1629073 (x : real) (y : real) : term12 x y.
Proof. exact (EQ_MP (@lem1629072 x y) (@lem1629071 x y)). Qed.
Lemma lem1629074 (x : real) (y : real) (z : real) : term13 x y z.
Proof. exact (@lem1629073 x y z). Qed.
Lemma lem1629075 (x : real) (z : real) (y : real) : (term13 x y z) = (term14 x z y).
Proof. exact (eq_refl (term13 x y z)). Qed.
Lemma lem1629076 (x : real) (z : real) (y : real) : term14 x z y.
Proof. exact (EQ_MP (@lem1629075 x z y) (@lem1629074 x y z)). Qed.
Lemma lem1629077 (z : real) (h1 : term6 z) : term6 z.
Proof. exact (h1). Qed.
Lemma lem1629078 (x : real) (y : real) (z : real) (h1 : term6 z) : (term15 x y z) = (term16 x z y).
Proof. exact (@lem1629076 x z y (@lem1629077 z h1)). Qed.
Lemma lem1629086 (x : real) (y : real) (h1 : (term17 y x) = (x = y)) : (term17 y x) = (x = y).
Proof. exact (h1). Qed.
Lemma lem1629087 (x : real) (y : real) (h1 : (term17 y x) = (x = y)) : (x = y) = (term17 y x).
Proof. exact (SYM (@lem1629086 x y h1)). Qed.
Lemma lem1629088 (y : real) (x : real) (h1 : (x = y) = (term17 y x)) : (x = y) = (term17 y x).
Proof. exact (h1). Qed.
Lemma lem1629089 (y : real) (x : real) (h1 : (x = y) = (term17 y x)) : (term17 y x) = (x = y).
Proof. exact (SYM (@lem1629088 y x h1)). Qed.
Lemma lem1629090 (y : real) (x : real) : ((term17 y x) = (x = y)) = ((x = y) = (term17 y x)).
Proof. exact (prop_ext (fun h1 : (term17 y x) = (x = y) => @lem1629087 x y h1) (fun h1 : (x = y) = (term17 y x) => @lem1629089 y x h1)). Qed.
Lemma lem1629091 (x : real) : (term18 x) = (term19 x).
Proof. exact (fun_ext (fun y : real => @lem1629090 y x)). Qed.
Lemma lem1629092 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629093 (x : real) : (term20 x) = (term21 x).
Proof. exact (MK_COMB (@lem1629092) (@lem1629091 x)). Qed.
Lemma lem1629094 : term22 = term23.
Proof. exact (fun_ext (fun x : real => @lem1629093 x)). Qed.
Lemma lem1629095 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629096 : term24 = term25.
Proof. exact (MK_COMB (@lem1629095) (@lem1629094)). Qed.
Lemma lem1629097 : term25.
Proof. exact (EQ_MP (@lem1629096) (@lem1339379)). Qed.
Lemma lem1629098 (x : real) : term26 x.
Proof. exact (@lem1629097 x). Qed.
Lemma lem1629099 (x : real) : (term26 x) = (term21 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1629100 (x : real) : term21 x.
Proof. exact (EQ_MP (@lem1629099 x) (@lem1629098 x)). Qed.
Lemma lem1629101 (x : real) (y : real) : term27 x y.
Proof. exact (@lem1629100 x y). Qed.
Lemma lem1629102 (y : real) (x : real) : (term27 x y) = ((x = y) = (term17 y x)).
Proof. exact (eq_refl (term27 x y)). Qed.
Lemma lem1629125 (y : real) (x : real) : (x = y) = (term17 y x).
Proof. exact (EQ_MP (@lem1629102 y x) (@lem1629101 x y)). Qed.
Lemma lem1629126 (y : real) (z : real) (x : real) : (x = (real_div y z)) = (term28 y z x).
Proof. exact (@lem1629125 (real_div y z) x). Qed.
Lemma lem1629129 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1629130 (y : real) (z : real) (x : real) : (term29 x y z) = (term30 y z x).
Proof. exact (MK_COMB (@lem1629129) (@lem1629126 y z x)). Qed.
Lemma lem1629134 (y : real) (x : real) : (x = y) = (term17 y x).
Proof. exact (EQ_MP (@lem1629102 y x) (@lem1629101 x y)). Qed.
Lemma lem1629135 (y : real) (x : real) (z : real) : ((real_mul x z) = y) = (term31 y x z).
Proof. exact (@lem1629134 y (real_mul x z)). Qed.
Lemma lem1629138 (y : real) (x : real) (z : real) : ((x = (real_div y z)) = ((real_mul x z) = y)) = ((term28 y z x) = (term31 y x z)).
Proof. exact (MK_COMB (@lem1629130 y z x) (@lem1629135 y x z)). Qed.
Lemma lem1629143 (z : real) : (term32 z) = (term32 z).
Proof. exact (eq_refl (term32 z)). Qed.
Lemma lem1629144 (y : real) (x : real) (z : real) : (term33 x z y) = (term34 y x z).
Proof. exact (MK_COMB (@lem1629143 z) (@lem1629138 y x z)). Qed.
Lemma lem1629147 (y : real) (x : real) : (term35 x y) = (term36 y x).
Proof. exact (fun_ext (fun z : real => @lem1629144 y x z)). Qed.
Lemma lem1629148 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629149 (y : real) (x : real) : (term37 x y) = (term38 y x).
Proof. exact (MK_COMB (@lem1629148) (@lem1629147 y x)). Qed.
Lemma lem1629154 (x : real) : (term39 x) = (term40 x).
Proof. exact (fun_ext (fun y : real => @lem1629149 y x)). Qed.
Lemma lem1629155 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629156 (x : real) : (term41 x) = (term42 x).
Proof. exact (MK_COMB (@lem1629155) (@lem1629154 x)). Qed.
Lemma lem1629161 : term43 = term44.
Proof. exact (fun_ext (fun x : real => @lem1629156 x)). Qed.
Lemma lem1629162 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629163 : term45 = term46.
Proof. exact (MK_COMB (@lem1629162) (@lem1629161)). Qed.
Lemma lem1629168 : term46 = term45.
Proof. exact (SYM (@lem1629163)). Qed.
Lemma lem1629184 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term47 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1629185 (p : Prop) (q : Prop) (p' : Prop) : term48 p q p'.
Proof. exact (fun q' : Prop => @lem1629184 p q p' q'). Qed.
Lemma lem1629186 (p : Prop) (q : Prop) : term49 p q.
Proof. exact (fun p' : Prop => @lem1629185 p q p'). Qed.
Lemma lem1629187 (y : real) (x : real) (z : real) : term50 y x z.
Proof. exact (@lem1629186 (term6 z) ((term28 y z x) = (term31 y x z))). Qed.
Lemma lem1629188 (y : real) (x : real) (z : real) (p' : Prop) : term51 y x z p'.
Proof. exact (@lem1629187 y x z p'). Qed.
Lemma lem1629189 (y : real) (x : real) (z : real) (p' : Prop) : (term51 y x z p') = (term52 y x z p').
Proof. exact (eq_refl (term51 y x z p')). Qed.
Lemma lem1629190 (y : real) (x : real) (z : real) (p' : Prop) : term52 y x z p'.
Proof. exact (EQ_MP (@lem1629189 y x z p') (@lem1629188 y x z p')). Qed.
Lemma lem1629191 (y : real) (x : real) (z : real) (p' : Prop) (q' : Prop) : term53 y x z p' q'.
Proof. exact (@lem1629190 y x z p' q'). Qed.
Lemma lem1629192 (y : real) (x : real) (z : real) (p' : Prop) (q' : Prop) : (term53 y x z p' q') = (term54 y x z p' q').
Proof. exact (eq_refl (term53 y x z p' q')). Qed.
Lemma lem1629193 (y : real) (x : real) (z : real) (p' : Prop) (q' : Prop) : term54 y x z p' q'.
Proof. exact (EQ_MP (@lem1629192 y x z p' q') (@lem1629191 y x z p' q')). Qed.
Lemma lem1629194 (z : real) : (term6 z) = (term6 z).
Proof. exact (eq_refl (term6 z)). Qed.
Lemma lem1629195 (y : real) (x : real) (z : real) (q' : Prop) : term55 y x z q'.
Proof. exact (@lem1629193 y x z (term6 z) q'). Qed.
Lemma lem1629196 (y : real) (x : real) (z : real) (q' : Prop) : term56 y x z q'.
Proof. exact (@lem1629195 y x z q' (@lem1629194 z)). Qed.
Lemma lem1629197 (z : real) (h1 : term6 z) : term6 z.
Proof. exact (h1). Qed.
Lemma lem1629198 (z : real) : (term6 z) = ((term6 z) = True).
Proof. exact (@lem7 (term6 z)). Qed.
Lemma lem1629205 (x : real) (z : real) (y : real) : term14 x z y.
Proof. exact (fun h0 : term6 z => @lem1629078 x y z h0). Qed.
Lemma lem1629207 (z : real) (h1 : term6 z) : (term6 z) = True.
Proof. exact (EQ_MP (@lem1629198 z) (@lem1629197 z h1)). Qed.
Lemma lem1629208 (z : real) (h1 : term6 z) : True = (term6 z).
Proof. exact (SYM (@lem1629207 z h1)). Qed.
Lemma lem1629209 (z : real) (h1 : term6 z) : term6 z.
Proof. exact (EQ_MP (@lem1629208 z h1) (@lem0)). Qed.
Lemma lem1629210 (x : real) (y : real) (z : real) (h1 : term6 z) : (term15 x y z) = (term16 x z y).
Proof. exact (@lem1629205 x z y (@lem1629209 z h1)). Qed.
Lemma lem1629211 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1629212 (x : real) (y : real) (z : real) (h1 : term6 z) : (term57 x y z) = (term58 x z y).
Proof. exact (MK_COMB (@lem1629211) (@lem1629210 x y z h1)). Qed.
Lemma lem1629214 (x : real) (y : real) (z : real) : term5 x y z.
Proof. exact (fun h0 : term6 z => @lem1629062 x y z h0). Qed.
Lemma lem1629215 (y : real) (x : real) (z : real) : term5 y x z.
Proof. exact (@lem1629214 y x z). Qed.
Lemma lem1629217 (z : real) (h1 : term6 z) : (term6 z) = True.
Proof. exact (EQ_MP (@lem1629198 z) (@lem1629197 z h1)). Qed.
Lemma lem1629218 (z : real) (h1 : term6 z) : True = (term6 z).
Proof. exact (SYM (@lem1629217 z h1)). Qed.
Lemma lem1629219 (z : real) (h1 : term6 z) : term6 z.
Proof. exact (EQ_MP (@lem1629218 z h1) (@lem0)). Qed.
Lemma lem1629220 (y : real) (x : real) (z : real) (h1 : term6 z) : (term7 y z x) = (term8 y x z).
Proof. exact (@lem1629215 y x z (@lem1629219 z h1)). Qed.
Lemma lem1629221 (y : real) (x : real) (z : real) (h1 : term6 z) : (term28 y z x) = (term31 y x z).
Proof. exact (MK_COMB (@lem1629212 x y z h1) (@lem1629220 y x z h1)). Qed.
Lemma lem1629224 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1629225 (y : real) (x : real) (z : real) (h1 : term6 z) : (term30 y z x) = (term59 y x z).
Proof. exact (MK_COMB (@lem1629224) (@lem1629221 y x z h1)). Qed.
Lemma lem1629230 (y : real) (x : real) (z : real) : (term31 y x z) = (term31 y x z).
Proof. exact (eq_refl (term31 y x z)). Qed.
Lemma lem1629231 (y : real) (x : real) (z : real) (h1 : term6 z) : ((term28 y z x) = (term31 y x z)) = ((term31 y x z) = (term31 y x z)).
Proof. exact (MK_COMB (@lem1629225 y x z h1) (@lem1629230 y x z)). Qed.
Lemma lem1629233 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1629234 (x : Prop) : (x = x) = True.
Proof. exact (@lem1629233 Prop x). Qed.
Lemma lem1629235 (y : real) (x : real) (z : real) : ((term31 y x z) = (term31 y x z)) = True.
Proof. exact (@lem1629234 (term31 y x z)). Qed.
Lemma lem1629236 (y : real) (x : real) (z : real) (h1 : term6 z) : ((term28 y z x) = (term31 y x z)) = True.
Proof. exact (TRANS (@lem1629231 y x z h1) (@lem1629235 y x z)). Qed.
Lemma lem1629237 (y : real) (x : real) (z : real) : term60 y x z.
Proof. exact (fun h0 : term6 z => @lem1629236 y x z h0). Qed.
Lemma lem1629238 (y : real) (x : real) (z : real) : term61 y x z.
Proof. exact (@lem1629196 y x z True). Qed.
Lemma lem1629239 (y : real) (x : real) (z : real) : (term34 y x z) = (term62 z).
Proof. exact (@lem1629238 y x z (@lem1629237 y x z)). Qed.
Lemma lem1629241 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1629242 (z : real) : (term62 z) = True.
Proof. exact (@lem1629241 (term6 z)). Qed.
Lemma lem1629243 (y : real) (x : real) (z : real) : (term34 y x z) = True.
Proof. exact (TRANS (@lem1629239 y x z) (@lem1629242 z)). Qed.
Lemma lem1629244 (y : real) (x : real) : (term36 y x) = term63.
Proof. exact (fun_ext (fun z : real => @lem1629243 y x z)). Qed.
Lemma lem1629245 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629246 (y : real) (x : real) : (term38 y x) = term64.
Proof. exact (MK_COMB (@lem1629245) (@lem1629244 y x)). Qed.
Lemma lem1629248 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1629249 (t : Prop) : (term66 t) = t.
Proof. exact (@lem1629248 real t). Qed.
Lemma lem1629250 : term64 = True.
Proof. exact (@lem1629249 True). Qed.
Lemma lem1629251 (y : real) (x : real) : (term38 y x) = True.
Proof. exact (TRANS (@lem1629246 y x) (@lem1629250)). Qed.
Lemma lem1629252 (x : real) : (term40 x) = term63.
Proof. exact (fun_ext (fun y : real => @lem1629251 y x)). Qed.
Lemma lem1629253 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629254 (x : real) : (term42 x) = term64.
Proof. exact (MK_COMB (@lem1629253) (@lem1629252 x)). Qed.
Lemma lem1629256 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1629257 (t : Prop) : (term66 t) = t.
Proof. exact (@lem1629256 real t). Qed.
Lemma lem1629258 : term64 = True.
Proof. exact (@lem1629257 True). Qed.
Lemma lem1629259 (x : real) : (term42 x) = True.
Proof. exact (TRANS (@lem1629254 x) (@lem1629258)). Qed.
Lemma lem1629260 : term44 = term63.
Proof. exact (fun_ext (fun x : real => @lem1629259 x)). Qed.
Lemma lem1629261 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629262 : term46 = term64.
Proof. exact (MK_COMB (@lem1629261) (@lem1629260)). Qed.
Lemma lem1629264 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1629265 (t : Prop) : (term66 t) = t.
Proof. exact (@lem1629264 real t). Qed.
Lemma lem1629266 : term64 = True.
Proof. exact (@lem1629265 True). Qed.
Lemma lem1629267 : term46 = True.
Proof. exact (TRANS (@lem1629262) (@lem1629266)). Qed.
Lemma lem1629268 : True = term46.
Proof. exact (SYM (@lem1629267)). Qed.
Lemma lem1629269 : term46.
Proof. exact (EQ_MP (@lem1629268) (@lem0)). Qed.
Lemma lem1629270 : term45.
Proof. exact (EQ_MP (@lem1629168) (@lem1629269)). Qed.
