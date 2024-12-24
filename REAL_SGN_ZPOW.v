Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SGN_ZPOW_term_abbrevs.
Require Import FORALL_INT_CASES_spec.
Require Import REAL_INV_SGN_spec.
Require Import REAL_SGN_INV_spec.
Require Import REAL_SGN_POW_spec.
Require Import REAL_ZPOW_POW_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3179995 (x : real) : term0 x.
Proof. exact (@lem1772483 x). Qed.
Lemma lem3179996 (x : real) : (term0 x) = ((term1 x) = (real_sgn x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem3179998 (x : real) : term2 x.
Proof. exact (@lem1734683 x). Qed.
Lemma lem3179999 (x : real) : (term2 x) = ((term3 x) = (real_sgn x)).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem3180003 (x : real) (n : nat) (h1 : (term4 x n) = (term5 x n)) : (term4 x n) = (term5 x n).
Proof. exact (h1). Qed.
Lemma lem3180004 (x : real) (n : nat) (h1 : (term4 x n) = (term5 x n)) : (term5 x n) = (term4 x n).
Proof. exact (SYM (@lem3180003 x n h1)). Qed.
Lemma lem3180005 (x : real) (n : nat) (h1 : (term5 x n) = (term4 x n)) : (term5 x n) = (term4 x n).
Proof. exact (h1). Qed.
Lemma lem3180006 (x : real) (n : nat) (h1 : (term5 x n) = (term4 x n)) : (term4 x n) = (term5 x n).
Proof. exact (SYM (@lem3180005 x n h1)). Qed.
Lemma lem3180007 (x : real) (n : nat) : ((term4 x n) = (term5 x n)) = ((term5 x n) = (term4 x n)).
Proof. exact (prop_ext (fun h1 : (term4 x n) = (term5 x n) => @lem3180004 x n h1) (fun h1 : (term5 x n) = (term4 x n) => @lem3180006 x n h1)). Qed.
Lemma lem3180008 (x : real) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun n : nat => @lem3180007 x n)). Qed.
Lemma lem3180009 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3180010 (x : real) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem3180009) (@lem3180008 x)). Qed.
Lemma lem3180011 : term10 = term11.
Proof. exact (fun_ext (fun x : real => @lem3180010 x)). Qed.
Lemma lem3180012 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3180013 : term12 = term13.
Proof. exact (MK_COMB (@lem3180012) (@lem3180011)). Qed.
Lemma lem3180014 : term13.
Proof. exact (EQ_MP (@lem3180013) (@lem1758099)). Qed.
Lemma lem3180015 (x : real) : term14 x.
Proof. exact (@lem3180014 x). Qed.
Lemma lem3180016 (x : real) : (term14 x) = (term9 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem3180017 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem3180016 x) (@lem3180015 x)). Qed.
Lemma lem3180018 (x : real) (n : nat) : term15 x n.
Proof. exact (@lem3180017 x n). Qed.
Lemma lem3180019 (x : real) (n : nat) : (term15 x n) = ((term5 x n) = (term4 x n)).
Proof. exact (eq_refl (term15 x n)). Qed.
Lemma lem3180021 : term16.
Proof. exact (proj2 (@lem3174260)). Qed.
Lemma lem3180022 (x : real) : term17 x.
Proof. exact (@lem3180021 x). Qed.
Lemma lem3180023 (x : real) : (term17 x) = (term18 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem3180024 (x : real) : term18 x.
Proof. exact (EQ_MP (@lem3180023 x) (@lem3180022 x)). Qed.
Lemma lem3180025 (x : real) (n : nat) : term19 x n.
Proof. exact (@lem3180024 x n). Qed.
Lemma lem3180026 (x : real) (n : nat) : (term19 x n) = ((term20 x n) = (term21 x n)).
Proof. exact (eq_refl (term19 x n)). Qed.
Lemma lem3180028 : term22.
Proof. exact (proj1 (@lem3174260)). Qed.
Lemma lem3180029 (x : real) : term23 x.
Proof. exact (@lem3180028 x). Qed.
Lemma lem3180030 (x : real) : (term23 x) = (term24 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem3180031 (x : real) : term24 x.
Proof. exact (EQ_MP (@lem3180030 x) (@lem3180029 x)). Qed.
Lemma lem3180032 (x : real) (n : nat) : term25 x n.
Proof. exact (@lem3180031 x n). Qed.
Lemma lem3180033 (x : real) (n : nat) : (term25 x n) = ((term26 x n) = (real_pow x n)).
Proof. exact (eq_refl (term25 x n)). Qed.
Lemma lem3180035 (P : int -> Prop) : term27 P.
Proof. exact (@lem2296993 P). Qed.
Lemma lem3180036 (P : int -> Prop) : (term27 P) = ((term28 P) = (term29 P)).
Proof. exact (eq_refl (term27 P)). Qed.
Lemma lem3180049 (P : int -> Prop) : (term28 P) = (term29 P).
Proof. exact (EQ_MP (@lem3180036 P) (@lem3180035 P)). Qed.
Lemma lem3180050 (x : real) : (term30 x) = (term31 x).
Proof. exact (@lem3180049 (term32 x)). Qed.
Lemma lem3180051 (x : real) (n : int) : (term33 x n) = ((term34 x n) = (term35 x n)).
Proof. exact (eq_refl (term33 x n)). Qed.
Lemma lem3180052 (x : real) : (term36 x) = (term32 x).
Proof. exact (fun_ext (fun n : int => @lem3180051 x n)). Qed.
Lemma lem3180053 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3180054 (x : real) : (term30 x) = (term37 x).
Proof. exact (MK_COMB (@lem3180053) (@lem3180052 x)). Qed.
Lemma lem3180055 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3180056 (x : real) : (term38 x) = (term39 x).
Proof. exact (MK_COMB (@lem3180055) (@lem3180054 x)). Qed.
Lemma lem3180057 (x : real) (n : nat) : (term40 x n) = ((term41 x n) = (term42 x n)).
Proof. exact (eq_refl (term40 x n)). Qed.
Lemma lem3180058 (x : real) : (term43 x) = (term44 x).
Proof. exact (fun_ext (fun n : nat => @lem3180057 x n)). Qed.
Lemma lem3180059 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3180060 (x : real) : (term45 x) = (term46 x).
Proof. exact (MK_COMB (@lem3180059) (@lem3180058 x)). Qed.
Lemma lem3180061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3180062 (x : real) : (term47 x) = (term48 x).
Proof. exact (MK_COMB (@lem3180061) (@lem3180060 x)). Qed.
Lemma lem3180063 (x : real) (n : nat) : (term49 x n) = ((term50 x n) = (term51 x n)).
Proof. exact (eq_refl (term49 x n)). Qed.
Lemma lem3180064 (x : real) : (term52 x) = (term53 x).
Proof. exact (fun_ext (fun n : nat => @lem3180063 x n)). Qed.
Lemma lem3180065 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3180066 (x : real) : (term54 x) = (term55 x).
Proof. exact (MK_COMB (@lem3180065) (@lem3180064 x)). Qed.
Lemma lem3180067 (x : real) : (term31 x) = (term56 x).
Proof. exact (MK_COMB (@lem3180062 x) (@lem3180066 x)). Qed.
Lemma lem3180068 (x : real) : ((term30 x) = (term31 x)) = ((term37 x) = (term56 x)).
Proof. exact (MK_COMB (@lem3180056 x) (@lem3180067 x)). Qed.
Lemma lem3180069 (x : real) : (term37 x) = (term56 x).
Proof. exact (EQ_MP (@lem3180068 x) (@lem3180050 x)). Qed.
Lemma lem3180081 (x : real) (n : nat) : (term26 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3180033 x n) (@lem3180032 x n)). Qed.
Lemma lem3180082 : real_sgn = real_sgn.
Proof. exact (eq_refl real_sgn). Qed.
Lemma lem3180083 (x : real) (n : nat) : (term41 x n) = (term4 x n).
Proof. exact (MK_COMB (@lem3180082) (@lem3180081 x n)). Qed.
Lemma lem3180084 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3180085 (x : real) (n : nat) : (term57 x n) = (term58 x n).
Proof. exact (MK_COMB (@lem3180084) (@lem3180083 x n)). Qed.
Lemma lem3180087 (x : real) (n : nat) : (term26 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3180033 x n) (@lem3180032 x n)). Qed.
Lemma lem3180088 (x : real) (n : nat) : (term42 x n) = (term5 x n).
Proof. exact (@lem3180087 (real_sgn x) n). Qed.
Lemma lem3180089 (x : real) (n : nat) : ((term41 x n) = (term42 x n)) = ((term4 x n) = (term5 x n)).
Proof. exact (MK_COMB (@lem3180085 x n) (@lem3180088 x n)). Qed.
Lemma lem3180092 (x : real) : (term44 x) = (term6 x).
Proof. exact (fun_ext (fun n : nat => @lem3180089 x n)). Qed.
Lemma lem3180093 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3180094 (x : real) : (term46 x) = (term8 x).
Proof. exact (MK_COMB (@lem3180093) (@lem3180092 x)). Qed.
Lemma lem3180101 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3180102 (x : real) : (term48 x) = (term59 x).
Proof. exact (MK_COMB (@lem3180101) (@lem3180094 x)). Qed.
Lemma lem3180112 (x : real) (n : nat) : (term20 x n) = (term21 x n).
Proof. exact (EQ_MP (@lem3180026 x n) (@lem3180025 x n)). Qed.
Lemma lem3180113 : real_sgn = real_sgn.
Proof. exact (eq_refl real_sgn). Qed.
Lemma lem3180114 (x : real) (n : nat) : (term50 x n) = (term60 x n).
Proof. exact (MK_COMB (@lem3180113) (@lem3180112 x n)). Qed.
Lemma lem3180115 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3180116 (x : real) (n : nat) : (term61 x n) = (term62 x n).
Proof. exact (MK_COMB (@lem3180115) (@lem3180114 x n)). Qed.
Lemma lem3180118 (x : real) (n : nat) : (term20 x n) = (term21 x n).
Proof. exact (EQ_MP (@lem3180026 x n) (@lem3180025 x n)). Qed.
Lemma lem3180119 (x : real) (n : nat) : (term51 x n) = (term63 x n).
Proof. exact (@lem3180118 (real_sgn x) n). Qed.
Lemma lem3180120 (x : real) (n : nat) : ((term50 x n) = (term51 x n)) = ((term60 x n) = (term63 x n)).
Proof. exact (MK_COMB (@lem3180116 x n) (@lem3180119 x n)). Qed.
Lemma lem3180123 (x : real) : (term53 x) = (term64 x).
Proof. exact (fun_ext (fun n : nat => @lem3180120 x n)). Qed.
Lemma lem3180124 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3180125 (x : real) : (term55 x) = (term65 x).
Proof. exact (MK_COMB (@lem3180124) (@lem3180123 x)). Qed.
Lemma lem3180132 (x : real) : (term56 x) = (term66 x).
Proof. exact (MK_COMB (@lem3180102 x) (@lem3180125 x)). Qed.
Lemma lem3180135 (x : real) : (term37 x) = (term66 x).
Proof. exact (TRANS (@lem3180069 x) (@lem3180132 x)). Qed.
Lemma lem3180136 : term67 = term68.
Proof. exact (fun_ext (fun x : real => @lem3180135 x)). Qed.
Lemma lem3180137 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3180138 : term69 = term70.
Proof. exact (MK_COMB (@lem3180137) (@lem3180136)). Qed.
Lemma lem3180145 : term70 = term69.
Proof. exact (SYM (@lem3180138)). Qed.
Lemma lem3180159 (x : real) (n : nat) : (term5 x n) = (term4 x n).
Proof. exact (EQ_MP (@lem3180019 x n) (@lem3180018 x n)). Qed.
Lemma lem3180160 (x : real) (n : nat) : (term58 x n) = (term58 x n).
Proof. exact (eq_refl (term58 x n)). Qed.
Lemma lem3180161 (x : real) (n : nat) : ((term4 x n) = (term5 x n)) = ((term4 x n) = (term4 x n)).
Proof. exact (MK_COMB (@lem3180160 x n) (@lem3180159 x n)). Qed.
Lemma lem3180163 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3180164 (x : real) : (x = x) = True.
Proof. exact (@lem3180163 real x). Qed.
Lemma lem3180165 (x : real) (n : nat) : ((term4 x n) = (term4 x n)) = True.
Proof. exact (@lem3180164 (term4 x n)). Qed.
Lemma lem3180166 (x : real) (n : nat) : ((term4 x n) = (term5 x n)) = True.
Proof. exact (TRANS (@lem3180161 x n) (@lem3180165 x n)). Qed.
Lemma lem3180167 (x : real) : (term6 x) = term71.
Proof. exact (fun_ext (fun n : nat => @lem3180166 x n)). Qed.
Lemma lem3180168 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3180169 (x : real) : (term8 x) = term72.
Proof. exact (MK_COMB (@lem3180168) (@lem3180167 x)). Qed.
Lemma lem3180171 {A : Type'} (t : Prop) : (term73 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3180172 (t : Prop) : (term74 t) = t.
Proof. exact (@lem3180171 nat t). Qed.
Lemma lem3180173 : term72 = True.
Proof. exact (@lem3180172 True). Qed.
Lemma lem3180174 (x : real) : (term8 x) = True.
Proof. exact (TRANS (@lem3180169 x) (@lem3180173)). Qed.
Lemma lem3180175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3180176 (x : real) : (term59 x) = (and True).
Proof. exact (MK_COMB (@lem3180175) (@lem3180174 x)). Qed.
Lemma lem3180184 (x : real) (n : nat) : (term5 x n) = (term4 x n).
Proof. exact (EQ_MP (@lem3180019 x n) (@lem3180018 x n)). Qed.
Lemma lem3180185 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem3180186 (x : real) (n : nat) : (term63 x n) = (term75 x n).
Proof. exact (MK_COMB (@lem3180185) (@lem3180184 x n)). Qed.
Lemma lem3180187 (x : real) (n : nat) : (term62 x n) = (term62 x n).
Proof. exact (eq_refl (term62 x n)). Qed.
Lemma lem3180188 (x : real) (n : nat) : ((term60 x n) = (term63 x n)) = ((term60 x n) = (term75 x n)).
Proof. exact (MK_COMB (@lem3180187 x n) (@lem3180186 x n)). Qed.
Lemma lem3180191 (x : real) : (term64 x) = (term76 x).
Proof. exact (fun_ext (fun n : nat => @lem3180188 x n)). Qed.
Lemma lem3180192 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3180193 (x : real) : (term65 x) = (term77 x).
Proof. exact (MK_COMB (@lem3180192) (@lem3180191 x)). Qed.
Lemma lem3180198 (x : real) : (term66 x) = (term78 x).
Proof. exact (MK_COMB (@lem3180176 x) (@lem3180193 x)). Qed.
Lemma lem3180200 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3180201 (x : real) : (term78 x) = (term77 x).
Proof. exact (@lem3180200 (term77 x)). Qed.
Lemma lem3180208 (x : real) : (term66 x) = (term77 x).
Proof. exact (TRANS (@lem3180198 x) (@lem3180201 x)). Qed.
Lemma lem3180209 : term68 = term79.
Proof. exact (fun_ext (fun x : real => @lem3180208 x)). Qed.
Lemma lem3180210 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3180211 : term70 = term80.
Proof. exact (MK_COMB (@lem3180210) (@lem3180209)). Qed.
Lemma lem3180216 : term80 = term70.
Proof. exact (SYM (@lem3180211)). Qed.
Lemma lem3180228 (x : real) : (term3 x) = (real_sgn x).
Proof. exact (EQ_MP (@lem3179999 x) (@lem3179998 x)). Qed.
Lemma lem3180229 (x : real) (n : nat) : (term60 x n) = (term4 x n).
Proof. exact (@lem3180228 (real_pow x n)). Qed.
Lemma lem3180230 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3180231 (x : real) (n : nat) : (term62 x n) = (term58 x n).
Proof. exact (MK_COMB (@lem3180230) (@lem3180229 x n)). Qed.
Lemma lem3180233 (x : real) : (term1 x) = (real_sgn x).
Proof. exact (EQ_MP (@lem3179996 x) (@lem3179995 x)). Qed.
Lemma lem3180234 (x : real) (n : nat) : (term75 x n) = (term4 x n).
Proof. exact (@lem3180233 (real_pow x n)). Qed.
Lemma lem3180235 (x : real) (n : nat) : ((term60 x n) = (term75 x n)) = ((term4 x n) = (term4 x n)).
Proof. exact (MK_COMB (@lem3180231 x n) (@lem3180234 x n)). Qed.
Lemma lem3180237 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3180238 (x : real) : (x = x) = True.
Proof. exact (@lem3180237 real x). Qed.
Lemma lem3180239 (x : real) (n : nat) : ((term4 x n) = (term4 x n)) = True.
Proof. exact (@lem3180238 (term4 x n)). Qed.
Lemma lem3180240 (x : real) (n : nat) : ((term60 x n) = (term75 x n)) = True.
Proof. exact (TRANS (@lem3180235 x n) (@lem3180239 x n)). Qed.
Lemma lem3180241 (x : real) : (term76 x) = term71.
Proof. exact (fun_ext (fun n : nat => @lem3180240 x n)). Qed.
Lemma lem3180242 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3180243 (x : real) : (term77 x) = term72.
Proof. exact (MK_COMB (@lem3180242) (@lem3180241 x)). Qed.
Lemma lem3180245 {A : Type'} (t : Prop) : (term73 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3180246 (t : Prop) : (term74 t) = t.
Proof. exact (@lem3180245 nat t). Qed.
Lemma lem3180247 : term72 = True.
Proof. exact (@lem3180246 True). Qed.
Lemma lem3180248 (x : real) : (term77 x) = True.
Proof. exact (TRANS (@lem3180243 x) (@lem3180247)). Qed.
Lemma lem3180249 : term79 = term81.
Proof. exact (fun_ext (fun x : real => @lem3180248 x)). Qed.
Lemma lem3180250 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3180251 : term80 = term82.
Proof. exact (MK_COMB (@lem3180250) (@lem3180249)). Qed.
Lemma lem3180253 {A : Type'} (t : Prop) : (term73 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3180254 (t : Prop) : (term83 t) = t.
Proof. exact (@lem3180253 real t). Qed.
Lemma lem3180255 : term82 = True.
Proof. exact (@lem3180254 True). Qed.
Lemma lem3180256 : term80 = True.
Proof. exact (TRANS (@lem3180251) (@lem3180255)). Qed.
Lemma lem3180257 : True = term80.
Proof. exact (SYM (@lem3180256)). Qed.
Lemma lem3180258 : term80.
Proof. exact (EQ_MP (@lem3180257) (@lem0)). Qed.
Lemma lem3180259 : term70.
Proof. exact (EQ_MP (@lem3180216) (@lem3180258)). Qed.
Lemma lem3180260 : term69.
Proof. exact (EQ_MP (@lem3180145) (@lem3180259)). Qed.
